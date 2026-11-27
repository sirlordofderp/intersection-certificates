"""Exact affine hull of a matched system with reciprocal binary dependencies."""
from collections import deque

from affine_shortfall import extract_core, representatives, satisfies
from parity_sat import indices, insert, lift, parity


def normalized(matched):
    """Translate the pivot model to zero and inspect options on the active pivot."""
    r = len(matched)
    origin = sum(next(b for a, b in c if a == 1 << i) << i for i, c in enumerate(matched))
    rows = []
    for i, clause in enumerate(matched):
        unit = 1 << i
        forms = {a ^ ((b ^ parity(a & origin)) << i) for a, b in clause} - {unit}
        if 0 in forms or any(a ^ unit in forms for a in forms):
            rows.append(0)
        elif len(forms) <= 1:
            rows.append(next(iter(forms), unit))
        else:
            return None
    if any((rows[j] >> i & 1) != (rows[i] >> j & 1)
           for i in range(r) for j in range(i)):
        return None
    return origin, rows


def hull_basis(rows):
    """Return independent actual models of x_i (Nx)_i = 0 for symmetric N."""
    n = len(rows)
    if any(a < 0 or a.bit_length() > n for a in rows) or any(
            (rows[i] >> j & 1) != (rows[j] >> i & 1) for i in range(n) for j in range(i)):
        raise ValueError("expected a symmetric binary square matrix")
    marked = {i for i in range(n) if rows[i] >> i & 1}
    basis, pivots = [], {}

    def add(x):
        if any(parity(rows[i] & x) for i in indices(x)):
            raise ArithmeticError("constructed path violates an active equation")
        if insert(x, 0, pivots)[0]:
            basis.append(x)

    for i in range(n):
        if i not in marked:
            add(1 << i)
    # Between successive marked vertices explore only unmarked interiors.
    # BFS gives induced paths, so their internal degrees are exactly two.
    for start in sorted(marked):
        queue = deque([start])
        paths = {start: 1 << start}
        while queue:
            i = queue.popleft()
            for j in indices(rows[i]):
                if j in paths:
                    continue
                paths[j] = paths[i] | (1 << j)
                if j in marked:
                    if start < j:
                        add(paths[j])
                else:
                    queue.append(j)
    return basis


def solve(n, clauses):
    """Decide a recognized reciprocal core with zero or one surplus clause."""
    clauses = [tuple(c) for c in clauses]
    if n < 0 or any(a < 0 or a.bit_length() > n or b not in (0, 1)
                    for c in clauses for a, b in c):
        raise ValueError("invalid affine input")
    selected, reached = representatives(clauses)
    basis, core = extract_core(clauses, selected, reached)
    r = len(basis)
    if len(core) - r > 1:
        return "OUTSIDE_CLASS", None
    data = normalized(core[:r])
    if data is None:
        return "OUTSIDE_CLASS", None
    origin, rows = data
    for y in [0, *hull_basis(rows)]:
        x = y ^ origin
        if satisfies(core[r:], x):
            witness = lift([(a, x >> j & 1) for j, a in enumerate(basis)]
                           + [o for i, o in selected.items() if i not in reached])
            if witness is None or not satisfies(clauses, witness):
                raise ArithmeticError("lift failed")
            return "SAT", witness
    return "UNSAT", None
