"""Reproduce the exhaustive checks, adversarial cases and structured instance."""
import json
from itertools import combinations, combinations_with_replacement, product
from math import comb
from random import Random
from clause_intervals import certified_count, dense_cnf, lower_family, representative_rows


def evaluation(clauses, row):
    return tuple(any(bool(row & (1 << (abs(l)-1))) == (l > 0) for l in c) for c in clauses)


def column_masks(clauses, rows):
    truth = [0] * len(clauses)
    count = 0
    for row in rows:
        for i, value in enumerate(evaluation(clauses, row)):
            if value:
                truth[i] |= 1 << count
        count += 1
    return truth, (1 << count)-1


def compare_patterns(full, sample, k):
    cols, all_rows = full
    scols, srows = sample
    ix = range(len(cols))
    for ends in combinations_with_replacement(ix, k+1):
        a, b = all_rows, srows
        for e in ends:
            a &= ~cols[e]
            b &= ~scols[e]
        if not a:
            continue
        for seps in combinations_with_replacement(ix, k):
            want, got = a, b
            for s in seps:
                want &= cols[s]
                got &= scols[s]
            assert bool(want) == bool(got), (ends, seps)


def verify(n, clauses):
    vals = [evaluation(clauses, s) for s in range(1 << n)]
    starts = [sum(not value and (i == 0 or values[i-1])
                  for i, value in enumerate(values)) for values in vals]
    full = column_masks(clauses, range(1 << n))
    for k in (1, 2):
        pool = representative_rows(n, clauses, k)
        compare_patterns(full, column_masks(clauses, pool), k)
        count, moments = certified_count(n, clauses, k)
        assert moments == [sum(comb(v, j) for v in starts) for j in range(k+2)]
        assert count == (starts.count(0) if max(starts) <= k else None)


def interval_block(r, first):
    return [tuple(range(first, first+i+1)) + tuple(range(first+r+i, first+2*r))
            for i in range(r)]


def main():
    # Every multiset of up to five canonical non-tautological clauses on 2 variables.
    canon = [tuple(sign*v for v, sign in enumerate(signs, 1) if sign)
             for signs in product((-1, 0, 1), repeat=2)]
    exhaustive = 0
    for size in range(6):
        for f in combinations_with_replacement(canon, size):
            verify(2, f)
            exhaustive += 1
    rng = Random(905005)
    for _ in range(160):
        n, m = rng.randint(1, 7), rng.randint(0, 9)
        f = [tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(5)))
             for _ in range(m)]
        rng.shuffle(f)
        verify(n, f)
    assert dense_cnf([(-10**80, 123), ()]) == (2, [(-2,1), ()])

    # All-uniform free bits miss the two-separator pattern on distinct free bits.
    trap = [(1,), (4,), (2,), (-5,), (3,)]
    def has_gap(rows):
        return any(evaluation(trap, a) == (False,True,False,True,False) for a in rows)
    assert not has_gap([0, (1<<3) | (1<<4)])
    assert has_gap(representative_rows(5, trap, 2))
    assert certified_count(5, trap, 2)[0] is None

    # One endpoint tuple forces one independent log(t) contribution.
    q, t = 3, 4
    n, f = lower_family(q, t)
    pool = representative_rows(n, f, 2)
    smallest = len(pool)
    for i, j, l in product(range(q), repeat=3):
        fiber = [a for a in pool if all(not evaluation(f, a)[v] for v in (i,q+j,2*q+l))]
        smallest = min(smallest, len(fiber))
        for x, y in product(range(t), repeat=2):
            if x != y:
                assert any(evaluation(f,a)[3*q+2*x] and evaluation(f,a)[3*q+2*y+1] for a in fiber)
    assert smallest >= (t-1).bit_length()
    r = 24
    f = interval_block(r, 1) + interval_block(r, 1+2*r)
    count, moments = certified_count(4*r, f, 2)
    expected = ((1 << (2*r)) - (r+1)*(1 << (r-2)))**2
    assert count == expected and moments[2] > 0 and moments[3] == 0
    report = dict(exhaustive_multisets=exhaustive, seeded_ordered_formulas=160, seed=905005,
                  uniform_completion_counterexample=trap,
                  lower_family=dict(q=q, probes=t, rows=len(pool), min_fiber=smallest),
                  structured=dict(variables=4*r, clauses=len(f), moments=moments, models=count))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
