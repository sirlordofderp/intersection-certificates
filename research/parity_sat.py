"""SAT from signed clause spectra, independent parity blocks, and a syndrome trellis.

Variables are 1..n. An affine observation (mask, rhs) fixes the parity selected
by mask, with bit 0 representing variable 1. A witness is a bit mask; None is UNSAT.
"""
from collections import defaultdict
from itertools import combinations

from clause_intervals import dense_cnf
from quotient_sat import normalize


def parity(x):
    return x.bit_count() % 2


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def reduce_row(row, label, pivots):
    """Remove pivot coordinates, applying the same XORs to the attached label."""
    for j in sorted(pivots, reverse=True):
        if row >> j & 1:
            v, a = pivots[j]
            row ^= v
            label ^= a
    return row, label


def insert(row, label, pivots):
    row, label = reduce_row(row, label, pivots)
    if row:
        pivots[row.bit_length()-1] = row, label
    return row, label


def lift(equations):
    pivots = {}
    for mask, rhs in equations:
        if insert(mask, rhs, pivots) == (0, 1):
            return None
    result = 0
    for j, (v, a) in sorted(pivots.items()):
        result |= (a ^ parity(result & v)) << j
    return result


def to_three(n, clauses):
    out = []
    for c in clauses:
        if len(c) <= 3:
            out.append(c)
            continue
        previous = 0
        for i in range(1, len(c)-2):
            n += 1
            out.append((previous or c[0], c[i], n))
            previous = -n
        out.append((previous, c[-2], c[-1]))
    return n, out


def spectrum(clauses):
    """Integer Walsh coefficients of eight times the number of false clauses."""
    coeff = defaultdict(int)
    for c in clauses:
        if len(c) > 3:
            raise ValueError("expected width at most three")
        for k in range(len(c)+1):
            for group in combinations(c, k):
                mask = sum(1 << (abs(v)-1) for v in group)
                sign = (-1)**sum(v < 0 for v in group)
                coeff[mask] += sign * (1 << (3-len(c)))
    return {m: a for m, a in coeff.items() if a}


def decompose(coeff):
    """Use a basis and fundamental circuits of the nonconstant Fourier support."""
    pivots, basis, terms = {}, [], []
    for mask, weight in sorted(coeff.items()):
        if not mask:
            continue
        rem, coords = reduce_row(mask, 0, pivots)
        if rem:
            unit = 1 << len(basis)
            pivots[rem.bit_length()-1] = rem, coords ^ unit
            basis.append(mask)
            coords = unit
        terms.append((coords, weight))
    parent = list(range(len(basis)))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for term, _ in terms:
        first, *rest = indices(term)
        for i in rest:
            parent[root(i)] = root(first)
    blocks = {}
    for i in range(len(basis)):
        blocks.setdefault(root(i), ([], []))[0].append(i)
    for term, weight in terms:
        blocks[root(next(indices(term)))][1].append((term, weight))
    return pivots, basis, list(blocks.values())


def projected_equations(evidence, spectral_pivots):
    """Eliminate physical directions invisible to the energy from affine evidence."""
    exterior, constraints = {}, {}
    for mask, rhs in evidence:
        rem, coords = reduce_row(mask, 0, spectral_pivots)
        residual, label = insert(rem, (coords << 1) | rhs, exterior)
        if not residual:
            if insert(label >> 1, label & 1, constraints) == (0, 1):
                return None
    return list(constraints.values())


def block_options(block, columns):
    variables, terms = block
    options = {}
    for row in range(1 << len(variables)):
        bits = syndrome = 0
        for j in indices(row):
            i = variables[j]
            bits |= 1 << i
            syndrome ^= columns[i]
        cost = sum(-a if parity(t & bits) else a for t, a in terms)
        if syndrome not in options or cost < options[syndrome][0]:
            options[syndrome] = cost, bits
    return options


def minimize(coeff, evidence):
    pivots, basis, blocks = decompose(coeff)
    eqs = projected_equations(evidence, pivots)
    if eqs is None:
        return None, dict(contradictory_evidence=True)
    target = sum(rhs << j for j, (_, rhs) in enumerate(eqs))
    columns = [sum(((m >> i) & 1) << j for j, (m, _) in enumerate(eqs))
               for i in range(len(basis))]
    # The suffix span tests whether a prefix syndrome has any completion.
    suffix = [{} for _ in range(len(blocks)+1)]
    for i in reversed(range(len(blocks))):
        suffix[i] = suffix[i+1].copy()
        for j in blocks[i][0]:
            insert(columns[j], 0, suffix[i])
    states = {0: (coeff.get(0, 0), 0)}
    prefix, widths = {}, [0]
    for i, block in enumerate(blocks):
        options = block_options(block, columns)
        nxt = {}
        for s, (cost, bits) in states.items():
            for t, (extra, local_bits) in options.items():
                combined = s ^ t
                if reduce_row(target ^ combined, 0, suffix[i+1])[0]:
                    continue
                total = cost + extra
                if combined not in nxt or total < nxt[combined][0]:
                    nxt[combined] = total, bits | local_bits
        states = nxt
        for j in block[0]:
            insert(columns[j], 0, prefix)
        width = len(prefix)+len(suffix[i+1])-len(eqs)
        if len(states) != 1 << width:
            raise ArithmeticError("syndrome state count differs from rank prediction")
        widths.append(width)
    minimum, coordinates = states[target]
    report = dict(blocks=len(blocks), max_block_rank=max((len(b[0]) for b in blocks), default=0),
                  support_rank=len(basis), evidence_rank=len(eqs), max_cut_rank=max(widths),
                  cut_ranks=widths)
    if minimum < 0:
        raise ArithmeticError("negative clause violation energy")
    if minimum:
        return None, report
    witness = lift([*evidence, *((v, (coordinates >> j) & 1) for j, v in enumerate(basis))])
    if witness is None:
        raise ArithmeticError("minimum has no physical lift")
    return witness, report


def solve(n, clauses, evidence=()):
    """Decide arbitrary dense CNF, optionally under simultaneous parity observations."""
    raw = [tuple(c) for c in clauses]
    evidence = list(evidence)
    if n < 0 or any(not 1 <= abs(v) <= n for c in raw for v in c):
        raise ValueError("expected variables in 1..n")
    if any(m < 0 or m.bit_length() > n or r not in (0, 1) for m, r in evidence):
        raise ValueError("invalid parity observation")
    clauses = normalize(raw)
    unit = [(1 << (abs(c[0])-1), int(c[0] > 0)) for c in clauses if len(c) == 1]
    fixed = [*evidence, *unit]
    ordinary = [c for c in clauses if len(c) != 1]
    # A single simultaneous pure-literal pass. An observed variable is protected.
    observed = 0
    for m, _ in fixed:
        observed |= m
    literals = {v for c in ordinary for v in c}
    pure = {v for v in literals if -v not in literals and not (observed >> (abs(v)-1) & 1)}
    ordinary = [c for c in ordinary if not any(v in pure for v in c)]
    fixed.extend((1 << (abs(v)-1), int(v > 0)) for v in sorted(pure))
    _, short = to_three(n, ordinary)
    witness, report = minimize(spectrum(short), fixed)
    if witness is not None:
        witness &= (1 << n)-1
        if not all(any(bool(witness >> (abs(v)-1) & 1) == (v > 0) for v in c) for c in raw):
            raise ArithmeticError("invalid SAT witness")
        if any(parity(witness & m) != rhs for m, rhs in evidence):
            raise ArithmeticError("invalid affine witness")
    return witness, report


def solve_cnf(clauses):
    """Decide CNF with arbitrary positive variable identifiers; return a named model."""
    raw = [tuple(c) for c in clauses]
    names = sorted({abs(v) for c in raw for v in c})
    n, dense = dense_cnf(raw)
    row, report = solve(n, dense)
    model = None if row is None else {v: bool(row >> i & 1) for i, v in enumerate(names)}
    return model, report


def masked_formula(n, clauses):
    """Encode each source clause with private selectors and masks. Pin the masks
    to zero to recover its models after forgetting the selectors."""
    encoded, pins = [], []
    size = n
    for clause in clauses:
        selectors = []
        for literal in clause:
            size += 2
            select, mask = size-1, size
            selectors.append(select)
            # select implies (truth of original literal) XOR mask.
            encoded.extend([(-select, literal, mask), (-select, -literal, -mask)])
            pins.append((-mask,))
        encoded.append(tuple(selectors))
    return size, encoded, pins
