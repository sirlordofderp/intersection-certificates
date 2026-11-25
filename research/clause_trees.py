"""Find an exact tree support for clause falsifiers, and count models on success."""
from itertools import combinations
from collections import defaultdict

from clause_intervals import clause_masks, dense_cnf, endpoint_cube


def normalize(clauses):
    nontrivial = {frozenset(c) for c in clauses}
    nontrivial = {c for c in nontrivial if not any(-lit in c for lit in c)}
    return [tuple(sorted(c)) for c in sorted(nontrivial, key=lambda a: (len(a), sorted(a)))
            if not any(d < c for d in nontrivial)]


def cube_size(n, masks, indices):
    zero, one = endpoint_cube(masks, indices)
    return 0 if zero & one else 1 << (n - (zero | one).bit_count())


def max_tree(n, masks):
    """Dense Prim with exact integer weights. Zero-weight edges are allowed."""
    m = len(masks)
    if not m:
        return []
    parent = [None] * m
    best = [-1] * m
    used = [False] * m
    best[0] = 0
    for _ in range(m):
        i = max((j for j in range(m) if not used[j]), key=best.__getitem__)
        used[i] = True
        for j in range(m):
            if not used[j]:
                weight = cube_size(n, masks, (i, j))
                if weight > best[j]:
                    best[j], parent[j] = weight, i
    return parent


def two_starts(n, masks, i, j, parent):
    """Count assignments on which two different vertices both start components."""
    anc = [p for p in (parent[i], parent[j]) if p is not None]
    size = cube_size(n, masks, (i, j))
    for p in anc:
        size -= cube_size(n, masks, (i, j, p))
    if len(anc) == 2:
        size += cube_size(n, masks, (i, j, *anc))
    return size


def count_with_tree(n, clauses):
    """Clauses use dense signed identifiers in 1..n. Preserve the supplied clauses.

    Return (number of models or None, parents, first pair of colliding starts or None).
    A collision on the maximizer rules out every exact tree on these vertices.
    """
    if n < 0 or any(not 1 <= abs(lit) <= n for c in clauses for lit in c):
        raise ValueError("variables must be in 1..n")
    masks = clause_masks(clauses)
    parent = max_tree(n, masks)
    for i, j in combinations(range(len(masks)), 2):
        if two_starts(n, masks, i, j, parent):
            return None, parent, (i, j)
    components = sum(cube_size(n, masks, (i,)) for i in range(len(masks)))
    components -= sum(cube_size(n, masks, (i, p))
                      for i, p in enumerate(parent) if p is not None)
    return (1 << n) - components, parent, None


def analyze(clauses):
    """Densify before normalization so variables eliminated from clauses still count."""
    n, dense = dense_cnf(clauses)
    return count_with_tree(n, normalize(dense))


def extremizer(width, k=1):
    """A subsumption-free width-w family with exactly k components on every row."""
    if min(width, k) < 1:
        raise ValueError("width and component count must be positive")
    clauses, parent = [], []
    for d in range(width+1):
        for word in range(1 << d):
            address = tuple((-(2*i+2) if word >> i & 1 else 2*i+2) for i in range(d))
            anchors = tuple(2*i+1 for i in range(d, width))
            clauses.append(address + anchors)
            parent.append(None if not d else (1 << (d-1))-1 + word % (1 << (d-1)))
    leaf_base = (1 << width)-1
    for r in range(k-1):
        for word in range(1 << width):
            p = leaf_base + word
            bit = word >> (width-1)
            fresh = 2*width + 2*r + bit + 1
            for lit in (fresh, -fresh):
                clauses.append(clauses[p][:-1] + (lit,))
                parent.append(p)
    return 2*(width+k-1), clauses, parent


def check_parents(parent, m):
    if len(parent) != m or sum(p is None for p in parent) != int(m > 0):
        raise ValueError("expected a rooted tree on the clauses")
    done = set()
    for i in range(m):
        path = set()
        v = i
        while v is not None and v not in done:
            if not isinstance(v, int) or not 0 <= v < m or v in path:
                raise ValueError("invalid parent or cycle")
            path.add(v)
            v = parent[v]
        done.update(path)


def cube_powers(n, clauses, parent, degree):
    """Signed subcube expansions of successive powers of the component count."""
    if n < 0 or any(not 1 <= abs(lit) <= n for c in clauses for lit in c):
        raise ValueError("variables must be in 1..n")
    masks = clause_masks(clauses)
    check_parents(parent, len(masks))
    terms = defaultdict(int)
    for i, p in enumerate(parent):
        terms[masks[i]] += 1
        if p is not None:
            terms[endpoint_cube(masks, (i, p))] -= 1
    terms = [(z, o, c) for (z, o), c in terms.items() if c and not z & o]
    powers = {(0, 0): 1}
    yield powers
    for _ in range(degree):
        product = defaultdict(int)
        for (z, o), value in powers.items():
            for z1, o1, coef in terms:
                if not (z & o1 or o & z1):
                    product[z | z1, o | o1] += value * coef
        powers = {cube: value for cube, value in product.items() if value}
        yield powers


def power_moments(n, clauses, parent, degree):
    """Return exact sums of powers without iterating assignments."""
    return [sum(value << (n - (z | o).bit_count()) for (z, o), value in power.items())
            for power in cube_powers(n, clauses, parent, degree)]


def root_polynomial(roots):
    q = [1]
    for root in roots:
        q = [x - root*y for x, y in zip([0] + q, q + [0])]
    return q


def spectral_count(n, clauses, parent, max_levels=2):
    """Return (model count, positive levels), or (None, None) for a wider spectrum.

    Test integer roots directly. Increasing degree ensures reported roots all occur.
    """
    if max_levels < 0:
        raise ValueError("expected a nonnegative level limit")
    max_levels = min(max_levels, len(clauses))
    mu = power_moments(n, clauses, parent, 2*max_levels+1)
    for d in range(max_levels+1):
        for roots in combinations(range(1, len(clauses)+1), d):
            q = root_polynomial(roots)
            residual = sum(a*b*mu[i+j+1] for i, a in enumerate(q) for j, b in enumerate(q))
            if residual == 0:
                num = sum(coef*mu[i] for i, coef in enumerate(q))
                count, rem = divmod(num, q[0])
                if rem:
                    raise ArithmeticError("nonintegral model count")
                return count, roots
    return None, None


def spectral_solve(n, clauses, parent, max_levels=2):
    """Return (model count, witness row or None, positive levels or None)."""
    count, roots = spectral_count(n, clauses, parent, max_levels)
    if not count:
        return count, None, roots
    q = root_polynomial(roots)
    indicator = defaultdict(int)
    for coef, power in zip(q, cube_powers(n, clauses, parent, len(roots))):
        for cube, a in power.items():
            indicator[cube] += coef*a
    zero = one = 0
    for i in range(n):
        try_zero = zero | (1 << i)
        mass = sum(a << (n - (z | o | try_zero | one).bit_count())
                   for (z, o), a in indicator.items() if not (z & one or o & try_zero))
        if mass*q[0] > 0:
            zero = try_zero
        else:
            one |= 1 << i
    return count, one, roots
