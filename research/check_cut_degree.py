"""Compare exact ranks of oriented-cut monomials with the edge-cover prediction."""
from fractions import Fraction
from itertools import combinations, permutations
import json
from random import Random

from clause_span import solve_linear
from quotient_sat import contract, count_models, lift_row, linear_links, quotient


def product_columns(n, arcs, d):
    all_rows = (1 << (1 << n))-1
    columns = {all_rows}
    flags = [sum(1 << x for x in range(1 << n) if (x >> u & 1) and not (x >> v & 1))
             for u, v in arcs]
    for _ in range(d):
        nxt = columns | {p & a for p in columns for a in flags}
        if nxt == columns:
            break
        columns = nxt
    return sorted(columns-{0})


def pivots(n, columns):
    basis = {}
    for col in columns:
        row = {i: Fraction(1) for i in range(1 << n) if col >> i & 1}
        while row:
            j = min(row)
            if j not in basis:
                v = row[j]
                basis[j] = {i: a/v for i, a in row.items()}
                break
            scale = row[j]
            for i, a in basis[j].items():
                b = row.get(i, 0)-scale*a
                if b:
                    row[i] = b
                else:
                    row.pop(i, None)
    return basis


def coverable(n, edges, d):
    unions = {0}
    ends = [(1 << i) | (1 << j) for i, j in edges]
    for _ in range(d):
        unions |= {u | e for u in unions for e in ends}
    return [s for s in range(1 << n) if any(s & ~u == 0 for u in unions)]


def connected(n, edges):
    active = {0}
    for _ in range(n):
        active |= {v for i, j in edges for u, v in ((i, j), (j, i)) if u in active}
    return len(active) == n


def graph_types(n):
    possible = list(combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(possible)):
        edges = tuple(e for i, e in enumerate(possible) if mask >> i & 1)
        if edges in seen or not connected(n, edges):
            continue
        for p in permutations(range(n)):
            seen.add(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in edges)))
        yield edges


def satisfies(clauses, row):
    return all(any(bool(row >> (abs(x)-1) & 1) == (x > 0) for x in c) for c in clauses)


def decoder(b, leaves):
    # Variables 1..b give an address; the next 2^b are data bits. Each
    # occurrence of address bit 1 uses a different signed copy around a star.
    m = 1 << b
    copies = [1] + [(b+m+i)*(1 if i%2 else -1) for i in range(1, leaves+1)]
    clauses = [c for s in copies[1:] for c in ((-1, s), (1, -s))]
    for j in range(m):
        address = [copies[j%len(copies)], *range(2, b+1)]
        clauses.append(tuple((-x if j >> i & 1 else x) for i, x in enumerate(address)) + (b+j+1,))
    return b+m+leaves, clauses


def mixed_clauses(scopes):
    return [tuple(-v if p >> i & 1 else v for i, v in enumerate(s))
            for s in scopes for p in range(1, (1 << len(s))-1)]


def exact_cover_instance(n, triples):
    """From triples on 1..3q to signed clauses of width exactly three."""
    scopes = list(triples)
    if n % 6 == 0:
        scopes.append((n+1, n+2, n+3))
        n += 3
    h, a, b = n+1, n+2, n+3
    scopes.append((h, a, b))
    scopes.extend((h, a, v) for v in range(1, n+1))
    return b, scopes, mixed_clauses(scopes)


def perfect_cover(n, scopes):
    masks = [sum(1 << (i-1) for i in s) for s in scopes]
    reachable = {0}
    for m in masks:
        reachable |= {r | m for r in reachable if not r & m}
    return (1 << n)-1 in reachable


def check_hardness():
    triples = [(i, j, k) for i in (1, 2) for j in (3, 4) for k in (5, 6)]
    positives = 0
    for mask in range(256):
        source = [t for j, t in enumerate(triples) if mask >> j & 1]
        answer = any(set(t).isdisjoint(u) for t, u in combinations(source, 2))
        n, scopes, clauses = exact_cover_instance(6, source)
        assert perfect_cover(n, scopes) == answer
        assert count_models(n, clauses, 0) == (2, 0)
        positives += answer
    # Independently solve the rational degree-2 membership problem on the
    # actual CNF truth table, once on each side of the threshold.
    for answer, source in [(False, []), (True, [(1, 2, 3)])]:
        n, _, clauses = exact_cover_instance(3, source)
        models = sum(1 << r for r in range(1 << n) if satisfies(clauses, r))
        assert models == 1 | (1 << ((1 << n)-1))
        atoms = [sum(1 << r for r in range(1 << n) if not satisfies([c], r)) for c in clauses]
        cols = sorted({(1 << (1 << n))-1, *atoms, *(a & b for a, b in combinations(atoms, 2))})
        assert (len(pivots(n, cols)) == len(pivots(n, [*cols, models]))) == answer
    return dict(tripartite_sources=256, positive_sources=positives,
                exact_width_three_rank_checks=2, quotient_model_counts_checked=256)


def check_linear():
    # Independent pointwise equations with signed targets, without the Gram matrix.
    rng = Random(88210)
    pairs = 0
    for _ in range(32):
        n = rng.randrange(2, 5)
        clauses = []
        for _ in range(rng.randrange(1, 7)):
            vs = rng.sample(range(1, n+1), rng.randint(1, n))
            clauses.append(tuple(rng.choice((-v, v)) for v in vs))
        links = linear_links(n, clauses)
        labels = {-a: b for a, b in links[::2]}
        literals = [x for i in range(1, n+1) for x in (i, -i)]
        for a, b in combinations(literals, 2):
            rows = [[int(not satisfies([c], r)) for c in clauses]
                    + [int(satisfies([(a,)], r))-int(satisfies([(b,)], r))]
                    for r in range(1 << n)]
            possible = solve_linear(rows, len(clauses)) is not None
            assert (labels.get(a, a) == labels.get(b, b)) == possible
            pairs += 1
    # Split each binary equality implication using its own independent guard.
    # The two halves sum to the old flag, but their variable scopes differ
    # between the forward and backward implications.
    b, leaves = 4, 15
    n, plain = decoder(b, leaves)
    clauses = []
    for c in plain:
        if len(c) == 2:
            n += 1
            clauses.extend([(*c, n), (*c, -n)])
        else:
            clauses.append(c)
    assert contract(n, clauses)[0] == n
    k, residual, _ = quotient(n, clauses)
    assert k == n-leaves and len(residual) == 1 << b
    count, witness = count_models(n, clauses, 1)
    assert count == 1 << (k-1) and satisfies(clauses, witness)
    return dict(pointwise_signed_pair_tests=pairs, split_decoder=dict(
        input_variables=n, input_clauses=len(clauses), syntactic_quotient_variables=n,
        linear_quotient_variables=k, residual_clauses=len(residual),
        input_degree_lower_bound=leaves, residual_degree=1, models=count, witness_checked=True))


def check_quotients():
    rng = Random(54139)
    cases = [(0, []), (0, [()]), (4, [(1, -1)]), (1, [(1,), (-1,)]),
             (4, [(-1, -2), (2, 3), (-3, 1), (-1, 4, 2)])]
    for k in range(3, 7):
        for p in (0, 1, (1 << k)//3):
            bucket = [tuple(-i if r >> (i-1) & 1 else i for i in range(1, k+1))
                      for r in range(1 << k) if r not in (p, ((1 << k)-1)^p)]
            cases.append((k+1, bucket))
            cases.append((k+1, bucket[1:]))
        almost = [tuple(-i if r >> (i-1) & 1 else i for i in range(1, k+1))
                  for r in range(2, 1 << k)]
        cases.append((k, almost))
    for _ in range(300):
        n = rng.randint(1, 7)
        cs = [tuple(rng.choice((-1, 1))*rng.randint(1, n) for _ in range(rng.randint(1, 4)))
              for _ in range(rng.randrange(10))]
        cases.append((n, cs))
    for n, cs in cases:
        truth = {r for r in range(1 << n) if satisfies(cs, r)}
        q = quotient(n, cs)
        if q is None:
            assert not truth
        else:
            k, residual, mapping = q
            lifts = [lift_row(mapping, r) for r in range(1 << k) if satisfies(residual, r)]
            assert len(lifts) == len(set(lifts)) and set(lifts) == truth
        count, witness = count_models(n, cs, 1)
        if count is not None:
            assert count == len(truth)
            assert witness in truth if truth else witness is None
    # Connected irredundant 3-CNF with no binary implications. Its guarded
    # petals realize the full clause trace when the guard and all y_i are zero.
    for m in range(2, 6):
        cs = [(1, 2+2*i, 3+2*i) for i in range(m)]
        assert count_models(2*m+1, cs, m-1) == (None, None)
        assert count_models(2*m+1, cs, m)[0] == 4**m + 3**m
    # The small instance also gets an independent exhaustive count.
    n, cs = decoder(2, 3)
    assert sum(satisfies(cs, r) for r in range(1 << n)) == count_models(n, cs, 1)[0]
    b, leaves = 5, 31
    n, cs = decoder(b, leaves)
    qn, residual, _ = quotient(n, cs)
    count, witness = count_models(n, cs, 1)
    assert qn == b+(1 << b) and len(residual) == 1 << b
    assert count == 1 << (qn-1) and satisfies(cs, witness)
    return dict(exhaustive_model_set_comparisons=len(cases), guarded_petal_sizes=[2, 3, 4, 5],
                decoder=dict(original_variables=n, original_clauses=len(cs), degree_lower_bound=leaves,
                             quotient_variables=qn, quotient_clauses=len(residual), degree=1,
                             models=count, witness_checked=True))


def main():
    graphs = checks = 0
    for n in range(2, 6):
        for edges in graph_types(n):
            graphs += 1
            arcs = [e for i, j in edges for e in ((i, j), (j, i))]
            for d in range(0, n):
                allowed = coverable(n, edges, d)
                cols = product_columns(n, arcs, d)
                rank = len(pivots(n, cols))
                # Every column agrees on the two constant rows. In the covered
                # Walsh space that is one independent linear equation for d>0.
                assert rank == len(allowed)-int(d > 0)
                consensus = 1 | (1 << ((1 << n)-1))
                expected = all(s in allowed for s in range(1 << n) if s.bit_count()%2 == 0)
                assert (len(pivots(n, [*cols, consensus])) == rank) == expected
                checks += 1
    # The oriented and unoriented variants already diverge on a triangle.
    tri = list(combinations(range(3), 2))
    xor_cols = [sum(1 << x for x in range(8) if ((x >> i) ^ (x >> j)) & 1) for i,j in tri]
    assert len(pivots(3, [255, *xor_cols])) == 4
    cycle = [(0,1), (1,2), (2,0)]
    assert len(pivots(3, product_columns(3, cycle, 1))) == 4
    assert len(pivots(3, product_columns(3, cycle+[(v,u) for u,v in cycle], 1))) == 6
    return dict(connected_graph_types=graphs, exact_rational_rank_cases=checks, quotient=check_quotients(),
                exact_cover=check_hardness(), linear_consequences=check_linear(),
                triangle_degree_one_dimensions=dict(unoriented=4, directed_cycle=4, bidirected=6))


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
