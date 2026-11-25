"""Truth-table, parity, rank and access-order checks. Only uses the Python standard library."""
from fractions import Fraction
from functools import cache
from itertools import product
import json
from math import comb
from random import Random

from clause_span import solve_linear
from intersection_order import affine_oracle, masks, project, validate


def table_oracle(pop):
    return cache(lambda q: sum(w for s, w in enumerate(pop) if s & q == q))


def check_table(pop, d):
    m = (len(pop)-1).bit_length()
    feat = list(masks(m, d))
    rows = ([int(s & t == t) for t in feat]+[1] for s in range(1, len(pop)) if pop[s])
    fits = solve_linear(rows, len(feat)) is not None
    moment = table_oracle(pop)
    queries = []

    def record(q):
        queries.append(q.bit_count())
        return moment(q)

    pr = project(m, d, record)
    assert max(queries, default=0) <= 2*d
    result = validate(pr, record)
    assert max(queries, default=0) <= 2*d+1
    assert result.exact_certificate == fits
    assert result.uncovered_min <= pop[0] <= result.uncovered_max
    assert not fits or pr.uncovered_under_promise == pop[0]
    gap = pr.uncovered_under_promise-pop[0]
    residual = 0
    for s, w in enumerate(pop):
        if s:
            value = sum(a for t, a in pr.coefficients.items() if t & s == t)
            residual += w*(1-value)**2
    assert residual == gap
    assert gap <= result.weighted_squared_error <= m*gap
    return not fits and result.uncovered_min == result.uncovered_max


def parity_oracle(n, m, p, guarded=False):
    # Independent forms with one private pivot each. All other non-guard bits
    # appear in exactly one form. The last form supplies the parity relation.
    limit = n-int(guarded)
    assert 2 <= m <= limit+1
    vectors = [0]*(m-1)
    for j in range(limit):
        vectors[j % (m-1)] |= 1 << j
    last = (1 << limit)-1
    events = [[(v, 1)] for v in vectors]+[[(last, 1 ^ p)]]
    if guarded:
        for e in events:
            e.append((1 << limit, 1))
    return affine_oracle(n, events)


def sharp_examples():
    cases = 0
    for d in range(1, 4):
        for m in (2*d, 2*d+1):
            for gate in (False, True):
                n = m-1+int(gate)
                a, b = [parity_oracle(n, m, p, gate) for p in (0, 1)]
                for s in range((1 << m)-1):
                    assert a(s) == b(s)
                checks = []
                for p, oracle in enumerate((a, b)):
                    pop = [int(s.bit_count()%2 == p) for s in range(1 << m)]
                    if gate:
                        pop[0] += 1 << (m-1)
                    direct = table_oracle(pop)
                    assert all(oracle(q) == direct(q) for q in range(1 << m))
                    pr = project(m, d, oracle)
                    checks.append(validate(pr, oracle).exact_certificate)
                    assert not checks[-1] or pr.uncovered_under_promise == pop[0]
                assert checks == [True, m == 2*d]
                cases += 1
    return cases


def block_check():
    cases = 0
    for t, m in ((1, 3), (2, 3), (3, 2)):
        low = (1 << t)-1
        populations = [[(s*s+3*s+1)%7 for s in range(1 << m)]]
        populations += [[int(s.bit_count()%2 == p) for s in range(1 << m)] for p in (0, 1)]
        tables = []
        for pop in populations:
            def decode(x):
                return sum(int(((x >> (i*t)) & low).bit_count()%2 == t%2) << i for i in range(m))
            raw = table_oracle([pop[decode(x)] for x in range(1 << (t*m))])
            macro = table_oracle(pop)
            for q in range(1 << (t*m)):
                blocks = [(q >> (i*t)) & low for i in range(m)]
                full = sum(int(v == low) << i for i, v in enumerate(blocks))
                free = sum(t-b.bit_count()-1 for b in blocks if b != low)
                assert raw(q) == macro(full) << free
                cases += 1
            tables.append((raw, macro))
        (ar, am), (br, bm) = tables[-2:]
        for k in range(t*m+1):
            assert all(ar(q) == br(q) for q in [0, *masks(t*m, k)]) == all(
                am(q) == bm(q) for q in [0, *masks(m, k//t)])
    return cases


def chain_checks():
    for m in range(1, 11):
        layers = []
        for p in (0, 1):
            # All m+1 chain patterns receive positive mass, so the inclusions
            # are strict and both systems have uncovered points.
            counts = [1 + (comb(m, k) if k % 2 == p else 0) for k in range(m+1)]
            data = [0]*(m+1)
            for q in range(1 << m):
                moment = sum(counts[q.bit_length():])
                data[q.bit_count()] += moment
            assert data == [sum(a*comb(k, j) for k, a in enumerate(counts)) for j in range(m+1)]
            assert sum((-1)**j*v for j, v in enumerate(data)) == counts[0] == 2-p
            layers.append(data)
        assert layers[0][:-1] == layers[1][:-1] and layers[0][-1] != layers[1][-1]
    return 10


def main():
    cases = rounded = 0
    for m in range(4):
        for pop in product(range(2), repeat=1 << m):
            for d in range(m+1):
                rounded += check_table(pop, d)
                cases += 1
    rng = Random(914261)
    for _ in range(96):
        m = rng.randrange(2, 6)
        pop = [rng.randrange(4) for _ in range(1 << m)]
        rounded += check_table(pop, rng.randrange(3))
        cases += 1
    large = []
    for p in (0, 1):
        oracle = parity_oracle(160, 6, p, guarded=True)
        pr = project(6, 3, oracle)
        val = validate(pr, oracle)
        expected = (1 << 159) + ((1 << 154) if p == 0 else 0)
        assert val.exact_certificate and pr.uncovered_under_promise == expected
        large.append(expected)
    # Inconsistent equations, empty events, zero-row constraints and shared pivots.
    a = affine_oracle(3, [[(1, 0), (1, 1)], [], [(0, 1)], [(3, 0), (6, 1), (5, 1)]])
    assert [a(q) for q in (0, 1, 2, 4, 8, 10)] == [8, 0, 8, 0, 2, 2]
    tiny = project(2, 1, table_oracle([1]*4))
    tv = validate(tiny, table_oracle([1]*4))
    assert tiny.uncovered_under_promise == Fraction(4, 3) and tv.weighted_squared_error == Fraction(4, 9)
    assert (tv.uncovered_min, tv.uncovered_max) == (1, 1)
    return dict(table_degree_cases=cases, exact_by_rounding_without_certificate=rounded,
                sharp_parity_pairs=sharp_examples(), block_moment_checks=block_check(),
                strict_chain_pairs=chain_checks(),
                affine_160_variable_uncovered=large)


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
