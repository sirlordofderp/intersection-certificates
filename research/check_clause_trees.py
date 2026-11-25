"""Independent truth-table checks for tree discovery, capacity and moment recovery."""
from collections import Counter
from itertools import combinations, product
import json
from random import Random

from clause_intervals import clause_masks, false_set
from clause_span import discover, solve, solve_cnf, solve_linear
from clause_trees import (analyze, check_parents, count_with_tree, extremizer,
                          normalize, power_moments, spectral_count, spectral_solve)


def components(active, parent):
    neighbors = {v: [] for v in active}
    for v in active:
        p = parent[v]
        if p in active:
            neighbors[v].append(p)
            neighbors[p].append(v)
    unseen = set(active)
    count = 0
    while unseen:
        stack = [unseen.pop()]
        count += 1
        while stack:
            for v in neighbors[stack.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
    return count


def parents_from_word(word, m):
    neighbors = [[] for _ in range(m)]
    live = set(range(m))
    for i, p in enumerate(word):
        leaf = min(live - set(word[i:]))
        neighbors[p].append(leaf)
        neighbors[leaf].append(p)
        live.remove(leaf)
    if len(live) == 2:
        a, b = live
        neighbors[a].append(b)
        neighbors[b].append(a)
    parent = [None]*m
    stack = [0] if m else []
    while stack:
        v = stack.pop()
        for u in neighbors[v]:
            if u != parent[v]:
                parent[u] = v
                stack.append(u)
    return parent


def truth(n, clauses):
    masks = clause_masks(clauses)
    return [false_set(masks, s) for s in range(1 << n)]


def compare_discovery(n, clauses):
    rows = truth(n, clauses)
    m = len(clauses)
    exists = any(all(components(row, p) <= 1 for row in rows)
                 for word in product(range(m), repeat=max(0, m-2))
                 for p in [parents_from_word(word, m)])
    result, p, collision = count_with_tree(n, clauses)
    assert exists == (result is not None)
    if exists:
        assert result == rows.count(frozenset()) and collision is None
    else:
        assert any(all(i in row and p[i] not in row for i in collision) for row in rows)
    return exists


def gated_spectrum(a, b):
    cores = [extremizer(1, k) for k in (a, b)]
    v = max(block[0] for block in cores) + 1
    clauses, parent = [], []
    for (_, cs, ps), guards in zip(cores, ((v, -v-1), (-v, v+1))):
        offset = len(clauses)
        clauses.extend(c+guards for c in cs)
        parent.extend((0 if offset else None) if p is None else p+offset for p in ps)
    return v+1, clauses, parent


def check_span(n, cs, degree):
    rows = truth(n, cs)
    # Independent feasibility oracle: literal truth table as the rows of the
    # pointwise system, retaining every index combination even if it is empty.
    features = [frozenset(idx) for d in range(1, degree+1)
                for idx in combinations(range(len(cs)), d)]
    oracle = solve_linear(([int(t <= row) for t in features]+[int(bool(row))] for row in rows),
                          len(features))
    count, witness, cert = solve(n, cs, degree)
    assert (oracle is not None) == (cert is not None)
    if cert is None:
        return False
    assert count == rows.count(frozenset())
    assert (witness is not None) == bool(count)
    if count:
        assert not rows[witness]
    for s, row in enumerate(rows):
        val = sum(a for (z, o), a in cert.items() if not (s & z or ~s & o))
        assert val == int(bool(row))
    return True


def main():
    literals = (1, -1, 2, -2)
    pool = [()] + [(v,) for v in literals] + list(product((1, -1), (2, -2)))
    exhaustive, span_tests = Counter(), Counter()
    for m in range(len(pool)+1):
        for cs in combinations(pool, m):
            if len(normalize(cs)) == m:
                exhaustive[str(compare_discovery(2, cs))] += 1
                for degree in range(3):
                    span_tests[str(check_span(2, cs, degree))] += 1
    rng = Random(421671)
    for _ in range(100):
        n, m = rng.randrange(1, 5), rng.randrange(7)
        cs = [tuple(rng.choice((-1, 1))*rng.randint(1, n)
                    for _ in range(rng.randrange(5))) for _ in range(m)]
        compare_discovery(n, cs)
        for degree in range(3):
            span_tests[str(check_span(n, cs, degree))] += 1
        p = parents_from_word([rng.randrange(m) for _ in range(max(0, m-2))], m)
        hist = Counter(components(r, p) for r in truth(n, cs))
        assert power_moments(n, cs, p, 5) == [
            sum(freq*c**j for c, freq in hist.items()) for j in range(6)]
        levels = tuple(sorted(set(hist)-{0}))
        for d in range(3):
            expect = (hist[0], levels) if len(levels) <= d else (None, None)
            assert spectral_count(n, cs, p, d) == expect
        count, witness, _ = spectral_solve(n, cs, p)
        if count:
            assert truth(n, cs)[witness] == frozenset()
        else:
            assert witness is None
    extreme_rows = 0
    for w, k in product(range(1, 5), range(1, 4)):
        n, cs, p = extremizer(w, k)
        assert len(cs) == k*(1 << (w+1))-1 == len(normalize(cs))
        assert all(len(c) == w for c in cs)
        check_parents(p, len(cs))
        rows = truth(n, cs)
        assert all(components(r, p) == k for r in rows)
        extreme_rows += len(rows)
        if k == 1:
            assert count_with_tree(n, cs)[0] == 0
            count = count_with_tree(n, cs[:-1])[0]
            assert count == sum(not (r-{len(cs)-1}) for r in rows) == 1 << (w-1)
    n, cs, p = gated_spectrum(4, 7)
    hist = Counter(components(r, p) for r in truth(n, cs))
    assert len(cs) == len(normalize(cs)) and all(len(c) == 3 for c in cs)
    assert spectral_count(n, cs, p, 1) == (None, None)
    count, witness, recovered = spectral_solve(n, cs, p, 2)
    assert (count, recovered) == (hist[0], (4, 7))
    assert not false_set(clause_masks(cs), witness)
    assert count_with_tree(n, cs)[0] is None
    auto, automatic_witness, cert = solve(n, cs, 1)
    assert auto == count and not false_set(clause_masks(cs), automatic_witness)
    for k in range(1, 7):
        units = [(v,) for v in range(1, k+1)]
        assert discover(k, units, k-1) is None
        exact, wit, full = solve(k, units, k)
        assert (exact, wit, len(full)) == (1, (1 << k)-1, (1 << k)-1)
    # Odd cycle of pairwise disequalities. Every assignment violates an odd
    # number of edge constraints. Supply only the ordinary 2-CNF input.
    cycle = [(sign*i, sign*(i % 5 + 1)) for i in range(1, 6) for sign in (-1, 1)]
    cycle_degrees = []
    for degree in range(1, 4):
        if check_span(5, cycle, degree):
            cycle_degrees.append(degree)
    assert cycle_degrees and solve(5, cycle, cycle_degrees[0])[0] == 0
    assert analyze([(1, -1), (2,), (2, 3)])[0] == 4
    assert solve_cnf([(10**100,), (-3,)], 2) == (1, {3: False, 10**100: True})
    for bad in ([1, 0], [None, 1], [None, None], [3, None]):
        try:
            check_parents(bad, 2)
        except ValueError:
            continue
        raise AssertionError(bad)
    return dict(exhaustive_two_variable_families=dict(exhaustive), random_cases=100,
                extremal_families=12, extremal_truth_rows=extreme_rows,
                span_feasibility_cases=dict(span_tests), independent_unit_sizes=list(range(1, 7)),
                odd_cycle_first_degree=cycle_degrees[0],
                spectral_example=dict(variables=n, clauses=len(cs),
                                      discovered_degree=1, nonzero_coefficients=len(cert),
                                      components_to_assignments=dict(sorted(hist.items()))))


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
