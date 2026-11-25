# How many assignments preserve the gaps between falsified CNF clauses?

For a CNF with **m clauses**, the worst-case number of actual assignments needed to preserve all feasible **false, true, false, true, false** patterns is **Θ(m³ log m)**. For the shorter **false, true, false** pattern the answer is **Θ(m²)**. One shared pool works for every choice and ordering of clauses. The proofs use the public repository's definitions of signed clauses and their evaluation.

This gives a polynomial-size representation of an exponential truth table for a specific task. In any proposed clause order, some assignment produces three separate runs of false clauses exactly when a row of the pool witnesses that condition. The same rows work after deleting or permuting clauses. For a supplied order in which every assignment has at most two false runs, there is also a polynomial-time exact model counter.

## Statement and proof

Index the clauses, including duplicates. A pool preserves a pattern if every tuple of clauses exhibiting that pattern on some assignment exhibits it on a pool row. The formal statement allows repeated indices. For m ≥ 1, let b be the least integer with 2ᵇ ≥ 2m². The upper bound is m³(2b + 2) rows.

**Upper bound.** Fix the three clauses required to be false. Every literal in them must be false. Conflicting requirements make the triple infeasible. Otherwise the requirements fix a subcube of assignments. Inside it, two further clauses must both be true. For each feasible ordered pair of these clauses select a jointly consistent pair of witness literals. Across all these pairs, at most 2m² variable names occur among the witnesses.

Give the selected variable names distinct b-bit addresses. Include the two constant background assignments. For each address position include the assignment that reads that position and its complement. When two witnesses require the same value, a constant background works. When they require different values, their variables are distinct, so some address bit distinguishes them. One orientation of that bit gives both desired values. Restore the fixed endpoint bits in all rows. Selected witnesses on fixed coordinates already agree with those bits. Repeating over all endpoint triples proves the bound. The implementation identifies witnesses by scanning literal pairs after applying the forced bits.

**Matching lower bound.** Take three banks of q clauses and t = 2ᵇ probe variables. A falsified clause within a bank identifies one value of a private code word. Two different clauses in a bank therefore cannot both be false. Include a positive guard g in each first-bank clause and a positive guard h in each second-bank clause. For each probe x, add the two clauses (x ∨ g) and (¬x ∨ h). This gives 3q + 2t clauses. The formula is satisfiable: set both guards true and choose an unused word in the third bank.

Fix one false clause from each bank. This selects one of q³ disjoint sets of assignments and forces both guards false. Within each set, for every two distinct probes x and y there is an assignment making the first probe true and the second false. Hence the column for x on this set's sample rows must differ from the column for y. With s rows there are at most 2ˢ different columns. Each set needs at least b rows, giving q³b in total. Taking q = t proves asymptotic tightness. Padding with duplicate clauses extends the bound to intermediate clause counts. The queries establishing the lower bound use distinct clauses, so they occur in genuine ordered subformulas. Lean uses one-hot words; the executable example uses ordinary binary words and reserves zero.

For the shorter pattern, use two constant completions per endpoint pair. Only one middle literal has to be true. Conversely, two banks and one true guard clause require a distinct sample row for each of q² endpoint pairs in a formula with 2q + 1 clauses.

These lower bounds apply to pools of actual assignments preserving every local pattern. An individual order or a symbolic representation can have a much shorter certificate.

## Exact counting and computational cost

Let R(s) count maximal false runs under assignment s, and let Mⱼ be the sum, over all assignments, of the binomial coefficient “R(s) choose j.” Every summand of M₃ is nonnegative. Thus M₃ = 0 precisely when the two-run condition holds. Substituting R = 0, 1, 2 gives the exact identity

    #SAT = 2ⁿ − M₁ + M₂.

Lean counts run ends with a true sentinel on the right. The implementation counts starts with a true sentinel on the left. Every nonempty run has one of each.

To compute Mⱼ without enumerating assignments, choose j candidate starts. Their clauses must all be false and their existing predecessors true. Expand the latter conditions by inclusion–exclusion in at most 2ʲ terms. Each term is the size of one intersection of falsification subcubes. It is zero for inconsistent forced bits, and otherwise equals 2ⁿ⁻ᵈ for d distinct forced variables. Through j = 3 this uses at most the sum of 2ʲ times “m choose j” subcube evaluations. Masks have n bits, and signed intermediates have O(n + log(m + 1)) bits for this fixed cap. A positive M₃ gives an “outside this class” result. The counter requires the clause order and works directly without building the representative pool.

For the pool construction let L be the total number of literal occurrences. For each of O(m³) endpoint choices, scanning candidate witness pairs costs O((L + m)²) literal-pair iterations. At most 2m² variable names are retained, and O(log(m + 1)) background assignments of n bits are produced. Sorting, checking literals, storing masks and constructing rows all have polynomial bit cost. Explicit pool storage is O(nm³ log(m + 1)) bits for rows, apart from bookkeeping. Sparse binary identifiers are renumbered using the provided dense_cnf function. Counts refer to the named variables; each separately declared unused variable gives a factor of two.

**Obstacle to unrestricted SAT.** With m independent positive unit clauses, every ordering admits an assignment falsifying alternate clauses. The same example works with disjoint three-literal clauses. Reaching unrestricted SAT by this route would require a transformation or decomposition that also bounds the total search and reconstruction work. Searching every permutation would cost factorial time.

## Verification and adversarial tests

The source imports PEqualNP.Defs.Search. Lean 4.36.0 accepted it at project commit cc5bff61fdb650a4ecd82694aeffa0f790a01a60 and Mathlib commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842. All eight audited declarations use only standard permitted axioms. Lean checks the bounds, the transfer to every order and subformula, and the model-count identity under the moment certificate. The subcube implementation and its runtime are justified by the analysis above and tested in Python. The Python code itself has not been formally verified. [Lean source](ClauseIntervals.lean) · [Verification transcript](../verification.json)

An independent oracle evaluated every assignment directly. It compared all feasible local patterns with those covered by the pool and checked every computed moment and count. Tests covered all **2,002 multisets** of zero through five clauses on two variables over the nine canonical non-tautological clauses, in canonical order, and **160 seeded ordered formulas** including repeated literals, tautologies and empty clauses. A five-unit-clause counterexample shows why two uniform completions per endpoint triple fail for the longer pattern. [Experiment code](check_experiments.py) · [Recorded results](experiments.json)

For the large check, clause i contains positive literals a₁ through aᵢ and bᵢ through bᵣ. Falsified indices form an interval: the a-condition holds on a prefix and the b-condition on a suffix. Each of the r clauses forbids 2^(r−1) assignments and adjacent clauses jointly forbid 2^(r−2), for r ≥ 2. Counting interval starts gives 2^(2r) − (r+1)2^(r−2) models per block. With two independent blocks and r = 24, the counter found M₃ = 0, M₂ > 0 and **79,228,103,484,694,296,839,256,539,136** models on 96 variables and 48 distinct clauses. This equals the square of the independent one-block count. [Model counter](clause_intervals.py)

From the workspace run the following commands to reproduce the results.

    python verify.py
    python -B research/check_experiments.py

## Frontier and novelty

L-alg-001 records the project's SAT-in-P target. The ledger marks the fixed-width resolution proposal and two proof-system claims refuted. L-alg-005 was retired and restated as L-alg-006, a conjectured lower bound for a syntactic integer proof system on binary pigeonhole formulas. This work takes an independent constructive route under L-alg-001. Both general SAT-in-P and the proof-system question remain open here. [Equality program](https://pequalnp.com/program#p_eq_np_search) · [L-alg-005](https://pequalnp.com/lemma#L-alg-005) · [L-alg-006](https://pequalnp.com/lemma#L-alg-006)

The candidate original result is the **matching bound on actual assignments needed to represent feasible clause-evaluation patterns of an arbitrary signed CNF**. The address construction uses established universal-set ideas. Standard cover-free families prescribe bits on selected coordinates. Here the queried coordinates are clause evaluations, and every row must arise from an assignment to the underlying variables. Constrained combinatorial testing likewise covers feasible tuples. The three independent endpoint choices and the logarithmic probe cost inside *each* disjoint set of assignments give the lower-bound product. [Naor, Schulman and Srinivasan](https://users.cms.caltech.edu/~schulman/Papers/splitters.pdf) · [Bshouty and Gabizon](https://arxiv.org/abs/1507.07368) · [Yamada et al.](https://people.kth.se/~artho/papers/yamada-2016.pdf)

Inclusion–exclusion for #SAT and methods parameterized by precisely satisfiable clause sets are established. The two-run condition concerns which clause positions a single assignment falsifies. Incidence-interval work places its ordering constraint on the variable–clause incidence graph. In the one-run case, the representative matrix can also be passed to a standard consecutive-ones recognizer to search column orders. [Clause-based inclusion–exclusion](https://home.cs.colorado.edu/~srirams/papers/sat11-mcount.pdf) · [Sæther, Telle and Vatshelle](https://arxiv.org/abs/1402.6485) · [Gaspers et al.](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.IPEC.2016.14) · [Booth and Lueker](https://www.cs.uoi.gr/~loukas/courses/grad/Algorithmic_Graph_Theory/index.files/Booth-Lueker-PQtrees.pdf)

A targeted search of these subjects, Mathlib and the public proof repository did not locate this extremal statement. The literature comparison supports reporting it as a candidate original contribution. Independent priority review remains open.
