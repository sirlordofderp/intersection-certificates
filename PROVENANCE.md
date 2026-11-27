# Research provenance

The repository is maintained by [sirlordofderp](https://github.com/sirlordofderp). The maintainer directed the research question, set the standards for originality and reproducibility, and authorized publication. OpenAI Codex proposed the conjectures, worked through the proofs and counterexamples, wrote the Lean and Python sources, ran the checks, and prepared the notes. This attribution describes the discovery process. It does not imply endorsement or human peer review by OpenAI, the Lean community, or the upstream project.

The work began with samples of actual assignments preserving patterns of falsified clauses. The next stage studied trees supporting those patterns and the certificate degree that a hidden tree guarantees. The present note asks what can be learned from labelled intersection sizes alone. The separation between promised counting and recognizing the promise emerged by comparing normal equations with a nonnegative residual, then constructing parity populations indistinguishable at the preceding order. The differential tests use direct pointwise equations and explicit small populations as reference calculations.

The subsequent [consensus study](research/CUT-DEGREE.md) began with exact rational ranks of products of oriented edge-cut indicators. Matching these ranks with the sets of variables covered by a bounded number of edges suggested a missing dimension at each degree. The proof used the bit pinned by a nonzero cut. Extending that argument to hyperedge patterns led to the Exact Cover reduction and to tests of signed-equality preprocessing against full model sets.

The [SAT decision study](research/PARITY-DECISION.md) arose from asking whether independent groups of parity coordinates persist when ordinary variables are fixed. Codex constructed the masked occurrence encoding and derived its shared-variable state count, then tested the solver against exhaustive search and formalized the mathematical core. The study credits the earlier Walsh, trellis, and compilation methods it uses.

The [affine-clause investigation](research/RECIPROCAL-HULL.md) began with one missing independent representative. Codex derived a randomized witness criterion and found that OpenAI Codex and Yichuan Wang had already published the same criterion with a faster algorithm. The related local implementation is a reproduction. Work then shifted to deterministic compilation, prescribed degree parities on induced subgraphs, and a row-perturbation criterion for the directed case. The local graph classification and reduction were developed in this investigation. The notes identify prior methods, what Lean checks, and which claims await independent review. [Earlier randomized algorithm](https://airaxiv.com/papers/pdf/2611.0031/?v=1)

## Dependencies and third-party material

Two source files reproduce the upstream project's literal and CNF semantics and their imports. They come from the pinned commit below. The local package and its mathematical claims are independent of the upstream project.

- [PEqualNP/Defs/Search.lean](PEqualNP/Defs/Search.lean) and [PEqualNP/Defs/ProofComplexity.lean](PEqualNP/Defs/ProofComplexity.lean) come from [open-goat/pequalnp-proofs at cc5bff6](https://github.com/open-goat/pequalnp-proofs/tree/cc5bff61fdb650a4ecd82694aeffa0f790a01a60/lean/PEqualNP/Defs). Their [Apache 2.0 license](third-party/pequalnp-LICENSE) is included.
- The package uses [Lean 4.36.0](https://github.com/leanprover/lean4/releases/tag/v4.36.0) and [Mathlib at fc4f59e](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842). The transitive dependency pins are recorded in [lake-manifest.json](lake-manifest.json).

The maintainer has licensed the original contributions in this repository under the [Apache License, Version 2.0](LICENSE). The third-party sources listed above retain their original attribution and license.

## Evidence and review

The [verification script](verify.py) reports the axioms of public research theorems from their built Lean modules and replays the Python suites. Its [recorded local run](verification.json) includes normalized source hashes and dependency versions. [CI](https://github.com/sirlordofderp/intersection-certificates/actions/workflows/verify.yml) runs the same checks on a clean Linux runner. The mathematical note identifies the theorem statements that Lean checks. The executable algorithms and complexity analyses have separate experimental and mathematical support.

Literature pointers are given alongside the corresponding claims in the notes. Corrections, references to prior results, and independent reproductions are welcome through the repository's issues.
