"""Enumerate every symmetric binary matrix through order five."""
from collections import Counter
from random import Random
import json
from itertools import product

from affine_shortfall import satisfies
from parity_sat import indices, insert, parity, reduce_row
from reciprocal_affine import hull_basis, normalized, solve


def codimension(rows):
    unseen = set(range(len(rows)))
    total = 0
    while unseen:
        stack = [unseen.pop()]
        marked = False
        while stack:
            i = stack.pop()
            marked |= bool(rows[i] >> i & 1)
            for j in indices(rows[i]):
                if j in unseen:
                    stack.append(j)
                    unseen.remove(j)
        total += marked
    return total


def minor_support(rows):
    answer = 0
    for s in range(1 << len(rows)):
        pivots = {}
        if all(insert(rows[i] & s, 0, pivots)[0] for i in indices(s)):
            answer |= 1 << s
    return answer


def excluded_weights(rows):
    """Exhaustive coefficient-support inclusion oracle; intentionally exponential."""
    original = minor_support(rows)
    found = set()
    for a in range(1 << len(rows)):
        for i in range(len(rows)):
            changed = list(rows)
            changed[i] ^= a
            if minor_support(changed) & ~original:
                found.add(a)
                break
    return found


def main():
    matrices = models = 0
    for n in range(6):
        cells = [(i, j) for i in range(n) for j in range(i + 1)]
        for mask in range(1 << len(cells)):
            rows = [0] * n
            for t in indices(mask):
                i, j = cells[t]
                rows[i] |= 1 << j
                rows[j] |= 1 << i
            basis = hull_basis(rows)
            pivots = {}
            for x in basis:
                assert insert(x, 0, pivots)[0]
            assert len(pivots) == n - codimension(rows)
            for x in range(1 << n):
                if all(not parity(rows[i] & x) for i in indices(x)):
                    assert reduce_row(x, 0, pivots)[0] == 0
                    models += 1
            matrices += 1
    rng = Random(1268704)
    outcomes = Counter()
    for _ in range(400):
        n = rng.randrange(1, 8)
        origin = rng.randrange(1 << n)
        rows = [0] * n
        for i in range(n):
            for j in range(i + 1):
                if rng.randrange(2):
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
        matched = [[(1 << i, origin >> i & 1), (a, parity(a & origin))] for i, a in enumerate(rows)]
        data = normalized(matched)
        assert data is not None
        extra = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(1, 4))]
        formula = [*matched, extra]
        status, x = solve(n, formula)
        expected = any(satisfies(formula, y) for y in range(1 << n))
        assert (status == "SAT") == expected and status in ("SAT", "UNSAT")
        if expected:
            assert satisfies(formula, x)
        outcomes[status] += 1
    # Directed cycle. Reciprocal necessity fails and the actual hull has rank one.
    rows = [3, 6, 5]
    actual = [x for x in range(8) if all(not parity(rows[i] & x) for i in indices(x))]
    assert actual == [0, 7]
    directed_queries = 0
    for n in range(4):
        for matrix in product(range(1 << n), repeat=n):
            points = [x for x in range(1 << n) if all(not parity(matrix[i] & x) for i in indices(x))]
            actual_weights = {a for a in range(1 << n) if any(parity(a & x) for x in points)}
            assert actual_weights == excluded_weights(matrix)
            directed_queries += 1 << n
    for _ in range(64):
        n = 4
        choices = [tuple(rng.sample(range(1 << n), 2)) for _ in range(n)]
        points = [x for x in range(1 << n)
                  if all(any(not parity(row & x) for row in choices[i]) for i in indices(x))]
        actual_weights = {a for a in range(1 << n) if any(parity(a & x) for x in points)}
        predicted = set().union(*(excluded_weights(m) for m in product(*choices)))
        assert actual_weights == predicted
    print(json.dumps(dict(symmetric_matrices=matrices, enumerated_models=models,
                          signed_solver_instances=outcomes, directed_cycle_models=actual,
                          directed_support_queries=directed_queries, multichoice_support_queries=64*16), indent=2))


if __name__ == "__main__":
    main()
