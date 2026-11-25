"""Exact CNF calculations. Variables are 1..n, literals are signed integers.

Callers with sparse external identifiers should use dense_cnf before these
operations. A row is the integer bit mask of its true variables.
"""
from itertools import combinations, combinations_with_replacement


def dense_cnf(clauses):
    variables = sorted({abs(lit) for c in clauses for lit in c})
    if variables and variables[0] == 0:
        raise ValueError("zero is not a literal")
    index = {v: i for i, v in enumerate(variables, 1)}
    return len(variables), [tuple(index[abs(lit)] * (1 if lit > 0 else -1)
                                  for lit in c) for c in clauses]


def clause_masks(clauses):
    result = []
    for clause in clauses:
        pos = neg = 0
        for lit in clause:
            bit = 1 << (abs(lit) - 1)
            if lit > 0:
                pos |= bit
            else:
                neg |= bit
        result.append((pos, neg))
    return result


def endpoint_cube(masks, ends):
    zeros = ones = 0
    for i in ends:
        pos, neg = masks[i]
        zeros |= pos
        ones |= neg
    return zeros, ones


def false_set(masks, row):
    return frozenset(i for i, (p, n) in enumerate(masks)
                     if not (p & row or n & ~row))


def representative_rows(n, clauses, k):
    """Preserve every realizable F,T,F (k=1) or F,T,F,T,F (k=2) pattern.

    Endpoint choices allow repetitions, which also covers smaller subfamilies.
    With two separators, keep one compatible witness pair per feasible pair
    of clauses. Then cover all binary patterns on pairs of those free bits.
    """
    if k not in (1, 2):
        raise ValueError("supported k are 1 and 2")
    masks = clause_masks(clauses)
    rows = set()
    for ends in combinations_with_replacement(range(len(clauses)), k + 1):
        zeros, ones = endpoint_cube(masks, ends)
        if zeros & ones:
            continue
        free = ((1 << n) - 1) & ~(zeros | ones)
        rows.update((ones, ones | free))
        if k == 1:
            continue
        # Each disjunction already guaranteed true can be dropped. Empty
        # residuals cannot participate in a satisfiable separator pair.
        residuals = []
        for c, (pos, neg) in zip(clauses, masks):
            if (pos & ones) or (neg & zeros):
                continue
            lits = [lit for lit in c if free & (1 << (abs(lit)-1))]
            if lits:
                residuals.append(lits)
        relevant = set()
        for a, b in combinations_with_replacement(residuals, 2):
            pair = next(((x, y) for x in a for y in b if x != -y), None)
            if pair is not None:
                relevant.update(abs(lit) for lit in pair)
        variables = sorted(relevant)
        for bit in range((max(1, len(variables))-1).bit_length()):
            stripe = sum(1 << (v-1) for j, v in enumerate(variables) if (j >> bit) & 1)
            rows.update((ones | stripe, ones | (free ^ stripe)))
    return rows


def certified_count(n, clauses, k):
    """Return (model count or None, factorial moments through k+1).

    None means an assignment falsifies more than k separate runs in the
    supplied order. No assignments are enumerated by this function.
    """
    masks = clause_masks(clauses)
    moments = [1 << n]
    for j in range(1, k + 2):
        total = 0
        for starts in combinations(range(len(clauses)), j):
            # Consecutive positions cannot both start a run.
            if any(b == a+1 for a, b in zip(starts, starts[1:])):
                continue
            parents = [i-1 for i in starts if i > 0]
            for h in range(len(parents)+1):
                for extra in combinations(parents, h):
                    zeros, ones = endpoint_cube(masks, starts + extra)
                    if not (zeros & ones):
                        total += (-1)**h * (1 << (n - (zeros | ones).bit_count()))
        moments.append(total)
    count = sum((-1)**j * v for j, v in enumerate(moments[:-1]))
    return (count if moments[-1] == 0 else None), moments


def lower_family(q, probes):
    """Three independent binary decoder banks and both polarities of each probe."""
    width = max(1, q.bit_length())  # reserve word zero, so the banks are satisfiable
    clauses = []
    g, h = 3*width + probes + 1, 3*width + probes + 2
    for bank in range(3):
        for word in range(1, q+1):
            code = tuple((bank*width + j + 1) * (-1 if word >> j & 1 else 1)
                         for j in range(width))
            clauses.append(code + ((g,) if bank == 0 else (h,) if bank == 1 else ()))
    for j in range(probes):
        v = 3*width+j+1
        clauses.extend([(v, g), (-v, h)])
    return 3*width+probes+2, clauses
