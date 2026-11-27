"""One-sided SAT search for affine clauses with bounded transversal deficiency.

An option (mask, rhs) is true at x iff parity(mask & x) == rhs.
No randomized failure is reported as a proof of unsatisfiability.
"""
from collections import deque
from itertools import combinations, product
from random import SystemRandom

from parity_sat import indices, insert, lift, parity, reduce_row


def representatives(clauses):
    """Maximum independent partial transversal and its final reachable colors."""
    selected = {}
    while True:
        pivots = {}
        for color, (mask, _) in selected.items():
            insert(mask, 1 << color, pivots)
        parent = {i: None for i in range(len(clauses)) if i not in selected}
        queue = deque(parent)
        augmented = False
        while queue and not augmented:
            i = queue.popleft()
            for option in clauses[i]:
                rem, used = reduce_row(option[0], 0, pivots)
                if rem:
                    selected[i] = option
                    while parent[i] is not None:
                        i, option = parent[i]
                        selected[i] = option
                    augmented = True
                    break
                for j in indices(used):
                    if j not in parent:
                        parent[j] = i, option
                        queue.append(j)
        if not augmented:
            return selected, set(parent)


def remainder(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


class BinaryField:
    """GF(2^d), built by trial division in GF(2)[t]."""
    def __init__(self, minimum):
        d = max(1, (minimum - 1).bit_length())
        self.size = 1 << d
        self.modulus = next(p for p in range(self.size + 1, 2 * self.size, 2)
                            if all(remainder(p, f) for k in range(1, d // 2 + 1)
                                   for f in range(1 << k, 2 << k)))

    def mul(self, a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & self.size:
                a ^= self.modulus
        return result

    def inv(self, a):
        if not a:
            raise ZeroDivisionError
        result, power = 1, self.size - 2
        while power:
            if power & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            power >>= 1
        return result


def maximal_minors(rows, field):
    """All minors deleting one column from a k by k+1 matrix, in column order."""
    k = len(rows)
    matrix = [list(row) for row in rows]
    pivots, scale = [], 1
    for col in range(k + 1):
        i = len(pivots)
        pivot = next((j for j in range(i, k) if matrix[j][col]), None)
        if pivot is None:
            continue
        matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
        a = matrix[i][col]
        scale = field.mul(scale, a)
        inverse = field.inv(a)
        matrix[i] = [field.mul(v, inverse) for v in matrix[i]]
        for j in range(k):
            if i != j and (factor := matrix[j][col]):
                matrix[j] = [u ^ field.mul(factor, v)
                             for u, v in zip(matrix[j], matrix[i])]
        pivots.append(col)
    result = [0] * (k + 1)
    if len(pivots) == k:
        free, = set(range(k + 1)).difference(pivots)
        result[free] = scale
        for i, col in enumerate(pivots):
            result[col] = field.mul(scale, matrix[i][free])
    return result


def moment(rows, field):
    """Boolean sum of the product of r+1 affine forms over r variables."""
    r = len(rows) - 1
    constants = [row[0] for row in rows]
    slopes = [row[1:] for row in rows]
    result = 0
    for c, d in zip(constants, maximal_minors(list(zip(*slopes)), field)):
        result ^= field.mul(c, d)
    for i, j in combinations(range(r + 1), 2):
        minors = maximal_minors([row for k, row in enumerate(slopes) if k not in (i, j)], field)
        for a, b, d in zip(slopes[i], slopes[j], minors):
            result ^= field.mul(field.mul(a, b), d)
    return result


def combine(clause, weights, rank):
    row = [0] * (1 + rank)
    for (mask, rhs), w in zip(clause, weights):
        if not rhs:
            row[0] ^= w
        for j in indices(mask):
            row[j + 1] ^= w
    return row


def satisfies(clauses, x):
    return all(any(parity(mask & x) == rhs for mask, rhs in clause) for clause in clauses)


def surplus_moment(rows, rank, field):
    """Mark each constant and each occurrence after a coordinate's first.

    Once those surplus slots are fixed, the unmarked slots form a permutation.
    A masked determinant enforces that each unmarked slot is its coordinate's first.
    """
    m = len(rows)
    if m == rank + 1:
        return moment(rows, field)
    result = 0
    for marked in combinations(range(m), m - rank):
        marked_set = set(marked)
        normal = [i for i in range(m) if i not in marked_set]
        for labels in product(range(rank + 1), repeat=len(marked)):
            first_repeat = [m] * (1 + rank)
            factor = 1
            for i, q in zip(marked, labels):
                factor = field.mul(factor, rows[i][q])
                if q:
                    first_repeat[q] = min(first_repeat[q], i)
            if not factor:
                continue
            # Append a zero column. Its cofactor is the square determinant.
            matrix = [[rows[i][q] if i < first_repeat[q] else 0
                       for q in range(1, rank + 1)] + [0] for i in normal]
            result ^= field.mul(factor, maximal_minors(matrix, field)[-1])
    return result


def extract_core(clauses, selected, reached):
    roots = sorted(reached.difference(selected))
    colors = sorted(reached.intersection(selected))
    basis = [selected[i][0] for i in colors]
    pivots = {}
    for j, mask in enumerate(basis):
        insert(mask, 1 << j, pivots)
    core = []
    for i in [*colors, *roots]:
        local = []
        for mask, rhs in clauses[i]:
            rem, coordinates = reduce_row(mask, 0, pivots)
            if rem:
                raise ArithmeticError("reachable core is not closed")
            local.append((coordinates, rhs))
        core.append(local)
    return basis, core


def solve(n, clauses, trials=3, rng=None, max_shortfall=1):
    """Return (status, witness). Status is SAT, NO_HIT, or OUTSIDE_PROMISE."""
    clauses = [tuple(c) for c in clauses]
    if n < 0 or trials < 1 or max_shortfall < 0 or any(mask < 0 or mask.bit_length() > n or rhs not in (0, 1)
                                  for c in clauses for mask, rhs in c):
        raise ValueError("invalid dimension, trial count, or affine equation")
    selected, reached = representatives(clauses)
    shortfall = len(clauses) - len(selected)
    if shortfall > max_shortfall:
        return "OUTSIDE_PROMISE", None
    if not shortfall:
        witness = lift(selected.values())
    else:
        basis, core = extract_core(clauses, selected, reached)
        rank = len(basis)
        field = BinaryField(4 * len(core))
        rng = SystemRandom() if rng is None else rng
        for _ in range(trials):
            rows = [combine(c, [rng.randrange(field.size) for _ in c], rank) for c in core]
            if surplus_moment(rows, rank, field):
                break
        else:
            return "NO_HIT", None
        equations = []
        for i, clause in enumerate(core):
            for option in clause:
                rows[i] = combine([option], [1], rank)
                if surplus_moment(rows, rank, field):
                    equations.append(option)
                    break
            else:
                raise ArithmeticError("nonzero multilinear moment lost during extraction")
        coordinates = lift(equations)
        if coordinates is None:
            raise ArithmeticError("odd intersection has no solution")
        witness = lift([(mask, (coordinates >> j) & 1) for j, mask in enumerate(basis)]
                       + [option for i, option in selected.items() if i not in reached])
    if witness is None or not satisfies(clauses, witness):
        raise ArithmeticError("physical witness failed independent evaluation")
    return "SAT", witness
