"""Build the pinned Lean package, audit its research theorems, and replay the experiments."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
RESEARCH = ROOT / "research"
MODULES = ("ClauseIntervals", "ClauseTrees", "ClauseSpan", "IntersectionOrder")
EXPERIMENTS = {
    "check_experiments.py": "experiments.json",
    "check_clause_trees.py": "tree-experiments.json",
    "check_intersection_order.py": "order-experiments.json",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(command, *, input_text=None, capture=True):
    result = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                            input=input_text, capture_output=capture)
    if result.returncode:
        if capture:
            sys.stderr.write(result.stdout + result.stderr)
        result.check_returncode()
    return result.stdout if capture else ""


def main():
    args = argparse.ArgumentParser()
    args.add_argument("--fetch-cache", action="store_true", help="fetch the imported Mathlib modules")
    args.add_argument("--report", type=Path, help="write machine-readable verification results")
    options = args.parse_args()
    lake = shutil.which("lake")
    if lake is None:
        lake = str(Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake"))
    if options.fetch_cache:
        files = list(RESEARCH.glob("*.lean")) + list((ROOT/"PEqualNP").rglob("*.lean"))
        imports = {i for f in files for i in re.findall(r"^import (Mathlib\.\S+)", f.read_text("utf-8"), re.M)}
        run([lake, "exe", "cache", "get", *sorted(imports)], capture=False)
    run([lake, "build"], capture=False)
    version = run([lake, "env", "lean", "--version"]).strip()
    pin = (ROOT/"lean-toolchain").read_text("utf-8").strip().rsplit(":v", 1)[-1]
    if f"version {pin}," not in version:
        raise RuntimeError("unexpected Lean version")
    manifest = json.loads((ROOT/"lake-manifest.json").read_text("utf-8"))
    mathlib_pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    installed = run(["git", "-C", str(ROOT/".lake/packages/mathlib"), "rev-parse", "HEAD"]).strip()
    if installed != mathlib_pin:
        raise RuntimeError("unexpected Mathlib revision")
    sources = {}
    names = []
    for m in MODULES:
        data = (RESEARCH/f"{m}.lean").read_bytes()
        source = data.decode("utf-8")
        sources[m] = sha256(source.replace("\r\n", "\n").encode()).hexdigest()
        names.extend(f"{m}.{name}" for name in re.findall(
            r"^(?:@\[[^\n]*?\]\s+)?(?:theorem|lemma)\s+([\w.']+)", source, re.M))
    code = "\n".join([*(f"import {m}" for m in MODULES), *(f"#print axioms {n}" for n in names)])
    audit = run([lake, "env", "lean", "--stdin"], input_text=code+"\n")
    if re.search(r"\b(error|warning):", audit):
        raise RuntimeError(audit)
    axioms = {}
    for n in names:
        match = re.search(rf"'{re.escape(n)}' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit)
        if not match:
            raise RuntimeError(f"missing audit for {n}")
        ax = sorted(v.strip() for v in (match.group(1) or "").split(",") if v.strip())
        if set(ax)-ALLOWED:
            raise RuntimeError(f"unexpected axioms for {n}: {ax}")
        axioms[n] = ax
    reports = {}
    for script, expected in EXPERIMENTS.items():
        report = json.loads(run([sys.executable, "-E", "-B", str(RESEARCH/script)]))
        if report != json.loads((RESEARCH/expected).read_text("utf-8-sig")):
            raise RuntimeError(f"{script} differs from {expected}")
        reports[script] = "matched"
    result = dict(lean=version, mathlib=installed, source_sha256_lf=sources, axioms=axioms, experiments=reports)
    if options.report:
        options.report.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"PASS. {len(names)} theorem audits and {len(reports)} experiment suites.")


if __name__ == "__main__":
    main()
