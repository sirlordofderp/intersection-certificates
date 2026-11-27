"""Independent truth-table and raw-choice checks for the affine SAT study."""
import json
from collections import Counter
from itertools import combinations, product
from random import Random

from affine_shortfall import BinaryField, combine, moment, representatives, satisfies, solve, surplus_moment
from parity_sat import insert, parity


def require(condition):
    if not condition:
        raise AssertionError("affine shortfall experiment failed")


def brute_moment(rows, r, field):
    total = 0
    for x in range(1 << r):
        value = 1
        for c, *a in rows:
            for j, weight in enumerate(a):
                if x >> j & 1:
                    c ^= weight
            value = field.mul(value, c)
        total ^= value
    return total


def rank(masks):
    pivots = {}
    for mask in masks:
        insert(mask, 0, pivots)
    return len(pivots)


def rado_deficiency(clauses):
    return max(len(group) - rank(a for j in group for a, _ in clauses[j])
               for k in range(len(clauses) + 1)
               for group in combinations(range(len(clauses)), k))


def exact_coefficients():
    options = list(product(range(1, 4), range(2)))
    groups = [c for k in range(3) for c in combinations(options, k)]
    masks = {o: sum(1 << x for x in range(4) if parity(o[0] & x) == o[1]) for o in options}
    total = Counter()
    for clauses in product(groups, repeat=3):
        sel, _ = representatives(clauses)
        require(3 - len(sel) == rado_deficiency(clauses))
        if len(sel) != 2:
            continue
        models = [x for x in range(4) if satisfies(clauses, x)]
        detects = any((masks[a] & masks[b] & masks[c]).bit_count() % 2
                      for a, b, c in product(*clauses))
        require(bool(models) == detects)
        total["sat" if models else "unsat"] += 1
    return dict(formulas=len(groups)**3, deficiency_one=dict(total))


def cancellation_example():
    # Find a non-tautological example where position-shared weights cancel
    # symbolically: every monomial grouped by number of second choices is even.
    groups = [((a, b), (c, d)) for a, c in combinations(range(1, 4), 2)
              for b, d in product(range(2), repeat=2)]
    for clauses in product(groups, repeat=3):
        nonzero = []
        for choices in product(range(2), repeat=3):
            fixed = [[c[j]] for c, j in zip(clauses, choices)]
            if sum(satisfies(fixed, x) for x in range(4)) % 2:
                nonzero.append(choices)
        if nonzero and all(k % 2 == 0 for k in Counter(map(sum, nonzero)).values()):
            return dict(clauses=clauses, odd_choices=nonzero)
    raise AssertionError("expected position-sharing cancellation")


def line_cover():
    lines = [(0, 1), (2, 4), (3, 7), (5, 6)]
    def outside(p, q):
        directions = [a for a in range(1, 8) if not parity(a & (p ^ q))]
        return [(a, 1 ^ parity(a & p)) for a in directions[:2]]
    return [outside(p, q) for p, q in lines]


def main():
    rng = Random(616027)
    evaluations = Counter()
    for r in range(5):
        for k in range(4):
            f = BinaryField(4 * (r + k + 1))
            for _ in range(32):
                rows = [[rng.randrange(f.size) for _ in range(r + 1)] for _ in range(r + k)]
                require(surplus_moment(rows, r, f) == brute_moment(rows, r, f))
                evaluations[str(k)] += 1
    outcomes = Counter()
    for _ in range(720):
        n = rng.randrange(6)
        clauses = [[(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(5))]
                   for _ in range(rng.randrange(8))]
        d = rado_deficiency(clauses)
        require(d == len(clauses) - len(representatives(clauses)[0]))
        truth = any(satisfies(clauses, x) for x in range(1 << n))
        status, witness = solve(n, clauses, trials=9, rng=rng, max_shortfall=2)
        if d > 2:
            require(status == "OUTSIDE_PROMISE")
        else:
            require((status == "SAT") == truth)
            if truth:
                require(satisfies(clauses, witness))
        outcomes[status] += 1
    cover = line_cover()
    require(rado_deficiency(cover) == 1 and not any(satisfies(cover, x) for x in range(8)))
    require(solve(3, cover, rng=rng)[0] == "NO_HIT")
    neighbor = [*cover[:-1], [(a, b ^ parity(a & 1)) for a, b in cover[-1]]]
    require(solve(3, neighbor, rng=rng)[0] == "SAT")
    # Core rank is smaller than the full rank; exterior equations must still lift.
    exterior = [*neighbor, [(9, 1), (16, 0)], [(33, 1)]]
    require(solve(6, exterior, rng=rng)[0] == "SAT")
    cycles = []
    for r in (2, 5, 9):
        clauses = [[(1 << i, 0), (1 << ((i + 1) % r), 1)] for i in range(r)]
        clauses.append([(1, 1)])
        require(solve(r, clauses, trials=9, rng=rng) == ("SAT", (1 << r) - 1))
        require(sum(satisfies(clauses, x) for x in range(1 << r)) == 1)
        cycles.append(r)
    print(json.dumps(dict(exhaustive=exact_coefficients(), field_evaluations_by_shortfall=evaluations,
                          random_instances=outcomes, shared_weight_counterexample=cancellation_example(),
                          line_cover_and_exterior_lift=True, unique_cycle_ranks=cycles), indent=2))


if __name__ == "__main__":
    main()
