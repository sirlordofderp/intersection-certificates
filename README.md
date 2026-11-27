# How much intersection data does exact counting need?

Suppose you know how many points lie in each of several events and in their labelled intersections. How many events must you intersect at a time to count the points outside their union?

There are two different answers. Suppose the union has a *pointwise inclusion–exclusion identity of degree d*. This means a single rational linear combination of intersections of at most d events takes value 1 on each covered point and 0 on each uncovered point.

| Task | Sharp worst-case intersection order |
| --- | --- |
| Compute the number of uncovered points, given the promise that a degree-d identity exists | **2d** |
| Decide whether any degree-d identity exists, and recover one on success | **2d+1** |
| Compute from only the *total* intersection size at each order, for m strictly nested events | **m**, even at degree one |

These thresholds hold for finite event systems, for every d ≥ 1, with the universe size given. Order counts the events in one intersection. The number of queries and the running time are polynomial in the number of events for **fixed** d when intersection sizes can be computed in polynomial time. A signed CNF clause is one application. Its event consists of the assignments on which that clause is false.

**See the gap with three events.** Write a point as its three membership bits. Compare the four even-parity patterns with the four odd-parity patterns. On either population, each event has size two and each pairwise intersection has size one. On the even population, half the sum of the three flags is an exact union indicator. On the odd population, the three singleton patterns force every coefficient to be one, but their sum at 111 is three. Even knowing *all* pairwise intersections cannot distinguish these cases.

The [research note](research/INTERSECTION-ORDER.md) gives the proof, sharp examples for every degree, a certified error interval when the promise fails, a parity encoding that multiplies the required intersection order, and the relationship to earlier literature. The [Lean source](research/IntersectionOrder.lean) formalizes the thresholds. The [Python implementation](research/intersection_order.py) works with an intersection-size function and includes an oracle for affine binary constraints.

## When the two models are easy and the certificate degree is hard

A connected family of three-variable scopes can encode the requirement that every variable has the same value. Its two satisfying assignments are immediate. On an even number of variables, the minimum degree of a polynomial in the original clause-falsification flags that recognizes those assignments is **exactly the minimum number of scopes covering all variables**. Deciding whether this degree meets an input threshold is NP-complete even for these width-three formulas. A polynomial-time change of variables counts the two models directly. [Mathematical note and reduction](research/CUT-DEGREE.md) · [Lean proof](research/CutDegree.lean) · [Executable counter](research/quotient_sat.py)

## SAT decision in hidden parity coordinates

The [SAT decision study](research/PARITY-DECISION.md) gives a deterministic solver for arbitrary CNF and an exact measure of one source of exponential work. Every 3-SAT instance is a restriction of a formula that splits into independent six-bit blocks after a change of parity coordinates. At each cut in the restricted construction, the solver retains exactly one state for every assignment to the original variables shared across the cut. [Lean theorems](research/ParityDecision.lean) · [Solver](research/parity_sat.py)

## Reproduce the results

Use Python 3.10 or newer, Git, and [Elan](https://github.com/leanprover/elan). From the repository root run

    python verify.py --fetch-cache

The script fetches the required Mathlib modules, builds with the pinned Lean 4.36.0 toolchain, inspects the axioms of the public research theorems, and replays five Python experiment suites against their recorded outputs. On a prepared checkout, `python verify.py` skips the cache download. To test the SAT decision results alone, run `python -B research/check_parity_sat.py`. The notes give time and space bounds for the algorithms. The exhaustive test oracles intentionally enumerate small populations.

[Local verification record](verification.json) · [Public verification runs](https://github.com/sirlordofderp/intersection-certificates/actions/workflows/verify.yml) · [New experiment output](research/order-experiments.json)

## Related results in this repository

- [Hidden clause trees and exact model counting](research/TREE-RESULT.md). If some arrangement of the clauses on a tree gives only d distinct positive component counts, a solver can count models from the CNF alone. The bound of 2d on the required **certificate degree** is sharp. That degree is a different quantity from the **oracle access order** in the table above.
- [Assignment samples for patterns of falsified clauses](research/RESULT.md). The worst-case sample size for preserving all realizable false–true–false–true–false patterns across clause orders is Θ(m³ log m).

## Status and provenance

This is an AI-assisted research note, open for mathematical review. Lean checked the listed theorem statements. The Python algorithms were differentially tested against exhaustive calculations. Independent peer review and historical priority remain open. The original motivation was the equality-side search for constructive SAT algorithms. The results give conditional algorithms and sharp information bounds, and general P versus NP remains open. [Attribution and licensing](PROVENANCE.md)

## License

The original research notes, Lean proofs, and Python code are licensed under the [Apache License, Version 2.0](LICENSE).
