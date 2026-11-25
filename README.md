# How much intersection data does exact counting need?

Suppose you know how many points lie in each of several events and in their labelled intersections. How many events must you intersect at a time to count the points outside their union?

There are two different answers. Suppose the union has a *pointwise inclusion–exclusion identity of degree d*. This means a single rational linear combination of intersections of at most d events takes value 1 on each covered point and 0 on each uncovered point.

| Task | Sharp worst-case intersection order |
| --- | --- |
| Compute the number of uncovered points, given the promise that a degree-d identity exists | **2d** |
| Decide whether any degree-d identity exists, and recover one on success | **2d+1** |

These thresholds hold for finite event systems, for every d ≥ 1, with the universe size given. Order counts the events in one intersection. The number of queries and the running time are polynomial in the number of events for **fixed** d when intersection sizes can be computed in polynomial time. A signed CNF clause is one application. Its event consists of the assignments on which that clause is false.

**See the gap with three events.** Write a point as its three membership bits. Compare the four even-parity patterns with the four odd-parity patterns. On either population, each event has size two and each pairwise intersection has size one. On the even population, half the sum of the three flags is an exact union indicator. On the odd population, the three singleton patterns force every coefficient to be one, but their sum at 111 is three. Even knowing *all* pairwise intersections cannot distinguish these cases.

The [research note](research/INTERSECTION-ORDER.md) gives the proof, sharp examples for every degree, a certified error interval when the promise fails, a parity encoding that multiplies the required intersection order, and the relationship to earlier literature. The [Lean source](research/IntersectionOrder.lean) formalizes the thresholds. The [Python implementation](research/intersection_order.py) works with an intersection-size function and includes an oracle for affine binary constraints.

## Reproduce the results

Use Python 3.10 or newer, Git, and [Elan](https://github.com/leanprover/elan). From the repository root run

    python verify.py --fetch-cache

The script fetches the required Mathlib modules, builds with the pinned Lean 4.36.0 toolchain, inspects the axioms of the public research theorems, and replays three Python experiment suites against their recorded outputs. On a prepared checkout, `python verify.py` skips the cache download. For the new experiments alone, run `python -B research/check_intersection_order.py`. The runtime and space requirements of the production algorithms are analyzed in the note. The exhaustive test oracles intentionally enumerate small populations.

[Local verification record](verification.json) · [Public verification runs](https://github.com/sirlordofderp/intersection-certificates/actions/workflows/verify.yml) · [New experiment output](research/order-experiments.json)

## Related results in this repository

- [Hidden clause trees and exact model counting](research/TREE-RESULT.md). If some arrangement of the clauses on a tree gives only d distinct positive component counts, a solver can count models from the CNF alone. The bound of 2d on the required **certificate degree** is sharp. That degree is a different quantity from the **oracle access order** in the table above.
- [Assignment samples for patterns of falsified clauses](research/RESULT.md). The worst-case sample size for preserving all realizable false–true–false–true–false patterns across clause orders is Θ(m³ log m).

## Status and provenance

This is an AI-assisted research note, open for mathematical review. Lean checked the listed theorem statements. The Python algorithms were differentially tested against exhaustive calculations. Independent peer review and historical priority remain open. The original motivation was the equality-side search for constructive SAT algorithms. The results give conditional algorithms and sharp information bounds, and general P versus NP remains open. [Attribution and licensing](PROVENANCE.md)
