"""Count after extracting consensus scopes and signed linear consequences."""
from fractions import Fraction

from clause_intervals import clause_masks
from clause_span import meet, solve, volume


def normalize(clauses):
    result = set()
    for clause in clauses:
        c = frozenset(clause)
        if not any(-x in c for x in c):
            result.add(tuple(sorted(c)))
    return sorted(result)


def components(adj, rev):
    """Kosaraju's algorithm with explicit DFS stacks."""
    seen = set()
    order = []
    for start in adj:
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(adj[start]))]
        while stack:
            v, successors = stack[-1]
            w = next(successors, None)
            if w is None:
                order.append(v)
                stack.pop()
            elif w not in seen:
                seen.add(w)
                stack.append((w, iter(adj[w])))
    label = {}
    for start in reversed(order):
        if start in label:
            continue
        label[start] = start
        todo = [start]
        while todo:
            for w in rev[todo.pop()]:
                if w not in label:
                    label[w] = start
                    todo.append(w)
    return label


def consensus_links(clauses):
    """Recognize truth tables allowing only two complementary local rows.

    Enumerate a table only when the input already contains all but two rows.
    Return entailed binary clauses for signed equality with the first variable.
    """
    groups = {}
    for c in clauses:
        if len(c) < 3:
            continue
        ordered = sorted(c, key=abs)
        scope = tuple(map(abs, ordered))
        row = sum(1 << i for i, x in enumerate(ordered) if x < 0)
        groups.setdefault(scope, set()).add(row)
    for scope, forbidden in groups.items():
        size = 1 << len(scope)
        if len(forbidden) != size-2:
            continue
        a, b = (i for i in range(size) if i not in forbidden)
        if a ^ b != size-1:
            continue
        root = scope[0]
        for j, v in enumerate(scope[1:], 1):
            lit = v if ((a >> j) ^ a) & 1 == 0 else -v
            yield -root, lit
            yield root, -lit


def linear_links(n, clauses):
    """Find literal equalities modulo the rational linear span of clause flags.

    Inner products on the Boolean cube are computed as box-intersection sizes.
    The flag span excludes an automatic constant term: we need zero on models.
    """
    if not clauses:
        return []
    variables = sorted({abs(lit) for c in clauses for lit in c})
    flags = clause_masks(clauses)
    bits = [(0, 1 << (v-1)) for v in variables]
    probes = [*flags, (0, 0), *bits]
    pivots = {}

    def remainder(box):
        row = [volume(n, meet(box, p)) for p in probes]
        for j in sorted(pivots):
            scale = row[j]
            if scale:
                row = [a-scale*b for a, b in zip(row, pivots[j])]
        return row

    for flag in flags:
        row = remainder(flag)
        j = next((i for i, a in enumerate(row) if a), None)
        if j is not None:
            scale = Fraction(row[j])
            pivots[j] = [a/scale for a in row]
    one = remainder((0, 0))
    representatives = {}
    links = []
    for v, bit in zip(variables, bits):
        pos = remainder(bit)
        neg = [a-b for a, b in zip(one, pos)]
        for lit, key in ((v, tuple(pos)), (-v, tuple(neg))):
            other = representatives.setdefault(key, lit)
            if other != lit:
                links.extend([(-lit, other), (lit, -other)])
    return links


def contract(n, clauses, extra=()):
    """Substitute signed classes from the binary graph and complete scope tables."""
    clauses = [tuple(c) for c in clauses]
    if n < 0 or any(not 1 <= abs(x) <= n for c in clauses for x in c):
        raise ValueError("variables must be in 1..n")
    clauses = normalize(clauses)
    if () in clauses:
        return None
    adj = {x: [] for i in range(1, n+1) for x in (i, -i)}
    rev = {x: [] for x in adj}
    def add_binary(a, b):
        for u, v in ((-a, b), (-b, a)):
            adj[u].append(v)
            rev[v].append(u)

    for c in clauses:
        if len(c) <= 2:
            add_binary(c[0], c[-1])
    for a, b in consensus_links(clauses):
        add_binary(a, b)
    for a, b in extra:
        add_binary(a, b)
    scc = components(adj, rev)
    signed = {}
    mapping = {}
    for i in range(1, n+1):
        a, b = scc[i], scc[-i]
        if a == b:
            return None
        if a not in signed:
            k = len(signed)//2 + 1
            signed[a], signed[b] = k, -k
        mapping[i], mapping[-i] = signed[a], signed[b]
    residual = normalize(tuple(mapping[x] for x in c) for c in clauses)
    return len(signed)//2, residual, tuple(mapping[i] for i in range(1, n+1))


def quotient(n, clauses):
    """Return (new n, residual, signed lift), or None for a proved contradiction."""
    first = contract(n, clauses)
    if first is None:
        return None
    k, residual, mapping = first
    extra = linear_links(k, residual)
    if not extra:
        return first
    second = contract(k, residual, extra)
    if second is None:
        return None
    size, final, signed = second
    lift = tuple(signed[abs(i)-1] * (1 if i > 0 else -1) for i in mapping)
    return size, final, lift


def lift_row(mapping, row):
    return sum(1 << i for i, lit in enumerate(mapping)
               if bool(row >> (abs(lit)-1) & 1) == (lit > 0))


def count_models(n, clauses, degree):
    """Return (count, original witness), (0, None), or (None, None) if inconclusive."""
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    q = quotient(n, clauses)
    if q is None:
        return 0, None
    size, residual, mapping = q
    count, row, _ = solve(size, residual, degree)
    return count, None if row is None else lift_row(mapping, row)
