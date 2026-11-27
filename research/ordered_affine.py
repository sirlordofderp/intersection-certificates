"""Deterministic representatives for a matched core and future affine clauses.

Matched clause i must contain a test with normal 1 << i. The general SAT
entry point obtains these coordinates by a maximum independent transversal.
"""
from itertools import combinations

from affine_shortfall import extract_core, representatives, satisfies
from parity_sat import insert, lift, parity, reduce_row


def feedback_basis(matched):
    """Minimum number of globally guessed parities for this ordered basis."""
    span, feedback = {}, []
    for i, clause in enumerate(matched):
        insert(1 << i, 0, span)
        for a, _ in clause:
            if insert(a, 0, span)[0]:
                feedback.append(a)
    return feedback


def transitions(matched, feedback):
    # Labels encode a prefix linear form (low r bits) and a linear form
    # on the guesses (high h bits). Always keep the distinguished pivot.
    rank = len(matched)
    pivots = {}
    for j, a in enumerate(feedback):
        insert(a, 1 << (rank + j), pivots)
    layers = []
    for i, clause in enumerate(matched):
        unit = 1 << i
        insert(unit, unit, pivots)
        base = next(b for a, b in clause if a == unit)
        choices = {(0, base)}
        for a, b in clause:
            rem, label = reduce_row(a, 0, pivots)
            if rem:
                raise ArithmeticError("feedback and prefix fail to span an option")
            if label & unit:
                choices.add((label ^ unit, b))
            else:
                # This option ignores the pivot. Toggle the baseline value
                # precisely when this option is true.
                choices.add((label, base ^ 1 ^ b))
        layers.append(sorted(choices))
    return layers


def monomials(n, degree):
    return [sum(1 << j for j in js) for d in range(min(n, degree) + 1)
            for js in combinations(range(n), d)]


def prune(points, features):
    """Keep actual points giving independent squarefree evaluation vectors."""
    pivots, retained = {}, []
    for x in points:
        row = sum(1 << i for i, s in enumerate(features) if x & s == s)
        if insert(row, 0, pivots)[0]:
            retained.append(x)
    return retained


def representative_models(matched, query_budget, max_degree=None):
    """A reusable list hitting every satisfiable extension by <= query_budget clauses.

    Returns (points or None, feedback basis). None indicates a resource cutoff.
    """
    r = len(matched)
    if query_budget < 0 or (max_degree is not None and max_degree < 0):
        raise ValueError("negative budget")
    for i, clause in enumerate(matched):
        if any(a < 0 or a.bit_length() > r or b not in (0, 1) for a, b in clause):
            raise ValueError("invalid matched option")
        if not any(a == 1 << i for a, _ in clause):
            raise ValueError("missing designated pivot")
    feedback = feedback_basis(matched)
    h = len(feedback)
    degree = min(r, h + query_budget)
    if max_degree is not None and degree > max_degree:
        return None, feedback
    layers = transitions(matched, feedback)
    features = monomials(r, degree)
    def closed_points():
        for guessed in range(1 << h):
            fixed = guessed << r
            points = [0]
            for i, choices in enumerate(layers):
                images = (x | ((parity(mask & (fixed | x)) ^ b) << i)
                          for x in points for mask, b in choices)
                points = prune(images, features)
            for x in points:
                if all(parity(a & x) == ((guessed >> j) & 1) for j, a in enumerate(feedback)):
                    yield x
    result = prune(closed_points(), monomials(r, query_budget))
    if any(not satisfies(matched, x) for x in result):
        raise ArithmeticError("retained point is not a matched model")
    return result, feedback


def solve(n, clauses, max_degree=None):
    """Deterministically decide a formula, optionally limiting the lifting degree."""
    clauses = [tuple(c) for c in clauses]
    if n < 0 or any(a < 0 or a.bit_length() > n or b not in (0, 1)
                    for clause in clauses for a, b in clause):
        raise ValueError("invalid affine input")
    selected, reached = representatives(clauses)
    basis, core = extract_core(clauses, selected, reached)
    r = len(basis)
    points, feedback = representative_models(core[:r], len(core) - r, max_degree)
    report = dict(core_rank=r, shortfall=len(core) - r, feedback_rank=len(feedback))
    if points is None:
        return "DEGREE_LIMIT", None, report
    report["representatives"] = len(points)
    for x in points:
        if satisfies(core[r:], x):
            witness = lift([(a, x >> j & 1) for j, a in enumerate(basis)]
                           + [o for i, o in selected.items() if i not in reached])
            if witness is None or not satisfies(clauses, witness):
                raise ArithmeticError("lift failed to satisfy the original formula")
            return "SAT", witness, report
    return "UNSAT", None, report
