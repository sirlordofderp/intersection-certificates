"""Discover a bounded-degree inclusion-exclusion formula from a densely numbered CNF."""
from fractions import Fraction

from clause_intervals import clause_masks, dense_cnf


def meet(a, b):
    return a[0] | b[0], a[1] | b[1]


def volume(n, box):
    z, o = box
    return 0 if z & o else 1 << (n - (z | o).bit_count())


def features(masks, degree):
    # Distinct nonempty intersections, grouped by the first degree that realizes them.
    atoms = sorted({(z, o) for z, o in masks if not z & o})
    seen = set()
    frontier = set(atoms)
    for d in range(1, min(degree, len(atoms))+1):
        seen.update(frontier)
        if d == degree or not frontier:
            break
        new = {meet(a, b) for a in frontier for b in atoms}
        frontier = {c for c in new if c not in seen and not c[0] & c[1]}
    return sorted(seen)


def solve_linear(rows, size):
    """Exact reduced pivots, with free coordinates set to zero. Accept singular systems."""
    pivots = {}
    for entries in rows:
        row = [Fraction(v) for v in entries]
        for j, pivot in sorted(pivots.items()):
            if row[j]:
                scale = row[j]
                row = [a-scale*b for a, b in zip(row, pivot)]
        j = next((i for i in range(size) if row[i]), None)
        if j is None:
            if row[-1]:
                return None
            continue
        scale = row[j]
        pivots[j] = [a/scale for a in row]
    x = [Fraction(0)] * size
    for j, row in sorted(pivots.items(), reverse=True):
        x[j] = row[-1] - sum(row[i]*x[i] for i in range(j+1, size))
    return x


def discover(n, clauses, degree):
    """Return the bad-row indicator as rationally weighted subcubes, or None.

    The exact equations are tested on all nonempty conjunctions through degree D+1.
    A solution is automatically a pointwise certificate. The empty dictionary is valid.
    """
    if n < 0 or degree < 0 or any(not 1 <= abs(lit) <= n for c in clauses for lit in c):
        raise ValueError("expected nonnegative degree and variables in 1..n")
    masks = clause_masks(clauses)
    basis = features(masks, degree)
    test = features(masks, degree+1)
    rows = ([volume(n, meet(a, b)) for b in basis] + [volume(n, a)] for a in test)
    sol = solve_linear(rows, len(basis))
    return None if sol is None else {a: v for a, v in zip(basis, sol) if v}


def solve(n, clauses, degree):
    """Count and construct a model, discovering the indicator directly from clauses."""
    cert = discover(n, clauses, degree)
    if cert is None:
        return None, None, None

    def models(box):
        v = volume(n, box) - sum(weight*volume(n, meet(box, a)) for a, weight in cert.items())
        if v.denominator != 1 or v < 0:
            raise ArithmeticError("invalid indicator")
        return int(v)

    count = models((0, 0))
    if not count:
        return 0, None, cert
    z = o = 0
    for i in range(n):
        if models((z | (1 << i), o)):
            z |= 1 << i
        else:
            o |= 1 << i
    return count, o, cert


def solve_cnf(clauses, degree):
    """Solve on the variables actually occurring, preserving original identifiers in the model."""
    clauses = [tuple(c) for c in clauses]
    variables = sorted({abs(lit) for c in clauses for lit in c})
    n, dense = dense_cnf(clauses)
    count, row, _ = solve(n, dense, degree)
    model = None if row is None else {v: bool(row >> i & 1) for i, v in enumerate(variables)}
    return count, model
