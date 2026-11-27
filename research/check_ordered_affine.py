"""Differential and sharpness checks for deterministic affine SAT compilation."""
from collections import Counter
from itertools import combinations, product
import json
from random import Random

from affine_shortfall import satisfies
from ordered_affine import feedback_basis, monomials, prune, representative_models, solve
from parity_sat import parity


def check(h):
    if not h:
        raise AssertionError("ordered affine regression")


def spaces(r):
    levels = {frozenset({0})}
    while levels:
        yield levels
        levels = {s.union(a ^ u for u in s) for s in levels for a in range(1 << r) if a not in s}


def sufficient(matched, space):
    return all(any((a ^ p) >> (i + 1) == 0 for p in space)
               for i, clause in enumerate(matched) for a, _ in clause)


def blocks(k, width):
    matched = []
    for _ in range(k):
        previous = 0
        for _ in range(width):
            unit = 1 << len(matched)
            matched.append([(unit, 0), (unit | previous, 1)])
            previous |= unit
    return matched


def main():
    rng = Random(190041)
    counts, exact, query_checks = Counter(), 0, 0
    for r in range(5):
        lattice = list(spaces(r))
        for _ in range(48):
            matched = [[(1 << i, rng.randrange(2))] +
                       [(rng.randrange(1 << r), rng.randrange(2)) for _ in range(rng.randrange(4))]
                       for i in range(r)]
            smallest = next(d for d, level in enumerate(lattice)
                            if any(sufficient(matched, s) for s in level))
            check(len(feedback_basis(matched)) == smallest)
            models = [x for x in range(1 << r) if satisfies(matched, x)]
            for k in range(3):
                points, _ = representative_models(matched, k)
                features = monomials(r, k)
                check(set(points) <= set(models))
                check(len(points) == len(prune(models, features)))
                equations = list(product(range(1 << r), range(2)))
                for fixed in combinations(equations, k):
                    def passes(x):
                        return all(parity(a & x) == b for a, b in fixed)
                    check(any(map(passes, models)) == any(map(passes, points)))
                    query_checks += 1
            exact += 1
    for _ in range(600):
        n = rng.randrange(7)
        clauses = [[(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(5))]
                   for _ in range(rng.randrange(9))]
        truth = any(satisfies(clauses, x) for x in range(1 << n))
        status, x, _ = solve(n, clauses)
        check(status == ("SAT" if truth else "UNSAT"))
        if truth:
            check(satisfies(clauses, x))
        counts[status] += 1
    sharp = []
    for k, b in [(1, 12), (2, 6), (3, 4)]:
        matched = blocks(k, b)
        points, h = representative_models(matched, k)
        all_models = {sum(1 << (i * b + j) for i, j in enumerate(js) if j < b)
                      for js in product(range(b + 1), repeat=k)}
        check(not h and all_models == set(points))
        for x in all_models:
            equations = []
            for i in range(k):
                block = ((1 << b) - 1) << (i*b)
                bit = x & block
                equations.append((bit or block, int(bool(bit))))
            check([y for y in all_models if all(parity(a & y) == v for a, v in equations)] == [x])
        sharp.append(dict(query_budget=k, block_size=b, forced_points=len(all_models), retained=len(points)))
    r = 24
    dense = [[(1 << i, 0), ((1 << r) - 1, 1)] for i in range(r)]
    points, h = representative_models(dense, 1)
    check(len(h) == 1 and len(points) == r + 1)
    paired = [[(1 << i, 0), (1 << (i ^ 1), 1)] for i in range(r)]
    check(len(feedback_basis(paired)) == r // 2)
    print(json.dumps(dict(exhaustive_subspace_minimum_tests=exact, exhaustive_flat_queries=query_checks,
                          full_solver_truth_tables=counts, sharp_examples=sharp,
                          dense_rank=r, dense_feedback=len(h), dense_retained=len(points),
                          paired_feedback=len(feedback_basis(paired))), indent=2))


if __name__ == "__main__":
    main()
