"""Exact union counting from labelled intersection cardinalities."""
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import ceil, floor

from clause_span import solve_linear


def masks(m, degree):
    for j in range(1, min(m, degree)+1):
        for indices in combinations(range(m), j):
            yield sum(1 << i for i in indices)


@dataclass
class Projection:
    event_count: int
    universe_size: int
    coefficients: dict
    union_lower_bound: Fraction

    @property
    def uncovered_under_promise(self):
        return self.universe_size - self.union_lower_bound


def project(m, degree, moment):
    """Order 2D. Its estimate is exact under the degree-D promise."""
    if m < 0 or degree < 0:
        raise ValueError("event and degree counts must be nonnegative")
    features = list(masks(m, degree))
    rows = ([moment(t | s) for s in features] + [moment(t)] for t in features)
    coeff = solve_linear(rows, len(features))
    if coeff is None:
        raise ValueError("inconsistent Gram data")
    a = {s: w for s, w in zip(features, coeff) if w}
    lower = sum((w*moment(s) for s, w in a.items()), Fraction(0))
    return Projection(m, moment(0), a, lower)


@dataclass(frozen=True)
class Validation:
    exact_certificate: bool
    weighted_squared_error: Fraction
    uncovered_min: int
    uncovered_max: int


def validate(projection, moment):
    """Order 2D+1. Also bound the integer answer when the certificate fails."""
    m, a = projection.event_count, projection.coefficients
    error = Fraction(0)
    for i in range(m):
        bit = 1 << i
        first = sum(w*moment(bit | s) for s, w in a.items())
        second = sum(v*w*moment(bit | s | t) for s, v in a.items() for t, w in a.items())
        error += moment(bit) - 2*first + second
    if error < 0:
        raise ValueError("inconsistent intersection data")
    estimate = projection.uncovered_under_promise
    lower = max(0, ceil(estimate-error))
    upper = min(projection.universe_size, floor(estimate-error/max(1, m)))
    if lower > upper:
        raise ValueError("inconsistent integer population")
    return Validation(not error, error, lower, upper)


def affine_oracle(n, events):
    """Each falsification event is a conjunction of (coefficient_mask, rhs) over F2.

    Bit positions index explicitly represented variables. All matrix operations use
    integer bit masks. The empty intersection is the entire n-dimensional space.
    """
    if n < 0:
        raise ValueError("expected nonnegative dimension")
    events = tuple(tuple(event) for event in events)
    for event in events:
        for v, b in event:
            if v < 0 or v.bit_length() > n or b not in (0, 1):
                raise ValueError("invalid binary affine equation")

    @cache
    def moment(t):
        if t < 0 or t.bit_length() > len(events):
            raise ValueError("invalid event mask")
        pivots = {}
        while t:
            bit = t & -t
            t ^= bit
            for v, b in events[bit.bit_length()-1]:
                while v:
                    j = v.bit_length()-1
                    if j not in pivots:
                        pivots[j] = (v, b)
                        break
                    w, c = pivots[j]
                    v, b = v ^ w, b ^ c
                else:
                    if b:
                        return 0
        return 1 << (n-len(pivots))
    return moment
