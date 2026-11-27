"""Differential tests for parity blocks, affine evidence, and the SAT embedding."""
from itertools import permutations
import json
from random import Random

from parity_sat import masked_formula, parity, solve, solve_cnf, spectrum


def true_clause(c, x):
    return any(bool(x >> (abs(v)-1) & 1) == (v > 0) for v in c)


def truth(n, cs, evidence=()):
    return next((x for x in range(1 << n) if all(true_clause(c, x) for c in cs)
                 and all(parity(x & m) == r for m, r in evidence)), None)


def cuts(cs):
    variables = [{abs(x) for x in c} for c in cs]
    return [len(set().union(*variables[:i]) & set().union(*variables[i:]))
            for i in range(len(cs)+1)]


def check():
    rng = Random(77781)
    sat = unsat = scores = 0
    for _ in range(560):
        n = rng.randrange(1, 8)
        cs = [tuple(rng.choice((-1, 1))*rng.randint(1, n)
                    for _ in range(rng.randrange(1, 8))) for _ in range(rng.randrange(14))]
        ev = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(5))]
        ref = truth(n, cs, ev)
        got, _ = solve(n, cs, ev)
        assert (ref is None) == (got is None)
        if got is None:
            unsat += 1
        else:
            sat += 1
        short = [tuple(sorted(set(c))) for c in cs if len(set(c)) <= 3 and not set(c) & {-v for v in c}]
        coeff = spectrum(short)
        for x in range(1 << n):
            assert sum((-a if parity(x & t) else a) for t, a in coeff.items()) == (
                8*sum(not true_clause(c, x) for c in short))
            scores += 1
    for n, cs, ev in [(0, [], []), (0, [()], []), (0, [], [(0, 1)]),
                      (8, [tuple(range(1, 9))], [(1 << i, 0) for i in range(8)]),
                      (8, [tuple(range(1, 9))], [(1 << i, int(i == 6)) for i in range(8)])]:
        assert (solve(n, cs, ev)[0] is None) == (truth(n, cs, ev) is None)
    huge = (1 << 200)+1
    assert solve_cnf([(huge,), (-huge, 3)])[0] == {3: True, huge: True}
    direct_sat = 0
    for _ in range(64):
        cs = [tuple(rng.choice((-v, v)) for v in rng.sample(range(1, 11), 3))
              for _ in range(46)]
        found, _ = solve(10, cs)
        assert (found is None) == (truth(10, cs) is None)
        direct_sat += found is not None
    # The pigeonhole principle in the original coordinates, without units or masks.
    for birds in (3, 4):
        cs = [tuple(3*p+h+1 for h in range(3)) for p in range(birds)]
        cs.extend((-3*p-h-1, -3*q-h-1) for p in range(birds)
                  for q in range(p) for h in range(3))
        found, _ = solve(3*birds, cs)
        assert (found is None) == (birds > 3)
    # All subfamilies of the eight ordinary signed triples, inspected with
    # and without pins. Also pin each original row on a smaller subset of cases.
    triples = [tuple(-v if p >> (v-1) & 1 else v for v in (1, 2, 3)) for p in range(8)]
    projections = 0
    for flags in range(256):
        cs = [c for j, c in enumerate(triples) if flags >> j & 1]
        n, base, pins = masked_formula(3, cs)
        x, info = solve(n, base)
        assert x is not None and info["max_block_rank"] == (6 if cs else 0)
        got, info = solve(n, base+pins)
        assert (got is None) == (truth(3, cs) is None)
        assert info["cut_ranks"] == cuts(cs)
        if flags % 17 == 0:
            for row in range(8):
                ev = [(1 << j, row >> j & 1) for j in range(3)]
                assert (solve(n, base+pins, ev)[0] is not None) == all(true_clause(c, row) for c in cs)
                projections += 1
    # Clauses at graph vertices, variables on graph edges. Here K4 has
    # three incident variables per vertex. Compare every cut in every order.
    stars = [(1, -2, 3), (-1, 4, 5), (2, -4, 6), (-3, -5, -6)]
    for order in permutations(stars):
        n, base, pins = masked_formula(6, order)
        _, info = solve(n, base+pins)
        assert info["cut_ranks"] == cuts(order)
    chain = [(i, -i-1, i+2) for i in range(1, 65)]
    n, base, pins = masked_formula(66, chain)
    x, info = solve(n, base+pins)
    assert x is not None and all(true_clause(c, x) for c in chain)
    assert info["cut_ranks"] == cuts(chain) and info["max_cut_rank"] == 2
    # The earlier common-guard example is handled by the ordinary pure-literal rule.
    petals = [(1, 2*i, 2*i+1) for i in range(1, 41)]
    p, pi = solve(81, petals)
    assert p is not None and pi["blocks"] == 0
    cycle_results = []
    length = 18
    for defect in (0, 1):
        source = []
        for i in range(length):
            v, w, guard = i+1, 1+(i+1)%length, length+i+1
            desired = int(i in (2, 7)) ^ (defect if i == length-1 else 0)
            for a in range(2):
                b = a ^ desired ^ 1
                for g in (guard, -guard):
                    source.append((-v if a else v, -w if b else w, g))
        nv, body, units = masked_formula(2*length, source)
        witness, stats = solve(nv, body+units)
        assert (witness is None) == bool(defect)
        assert stats["cut_ranks"] == cuts(source)
        cycle_results.append(dict(sat=witness is not None, variables=nv, clauses=len(body+units),
                                  max_cut_rank=stats["max_cut_rank"]))
    return dict(random_cases=dict(sat=sat, unsat=unsat), direct_energy_checks=scores,
                unmasked_random_three_cnf=dict(sat=direct_sat, unsat=64-direct_sat,
                                               variables=10, clauses_per_case=46),
                direct_pigeonhole_cases=2,
                boundary_cases=6, wrapper_subfamilies=256, pinned_original_rows=projections,
                all_orders_of_four_vertex_graph=24, guarded_petals=40, signed_cycles=cycle_results,
                chain=dict(variables=n, ordinary_clauses=len(base), unit_pins=len(pins),
                           blocks=info["blocks"], block_rank=info["max_block_rank"],
                           projected_evidence_rank=info["evidence_rank"],
                           max_cut_rank=info["max_cut_rank"], max_retained_states=1 << info["max_cut_rank"]))


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
