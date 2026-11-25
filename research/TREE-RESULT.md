# Counting SAT models without finding the clause tree

Suppose the clauses of a signed CNF can be placed on a tree. Under each assignment, retain just the falsified clauses and the edges between them. If the resulting forest has only **d distinct positive component counts** across all assignments, there is a deterministic algorithm to **count all models and find a satisfying assignment**, given just the CNF and the bound d. The tree, the counts, and a sample of assignments are unnecessary inputs. The algorithm runs in polynomial time for each fixed d. An instance with 4 or 7 components on its nonsatisfying rows has d = 2.

The proof gives a more general, directly decidable condition. In polynomial time for fixed D, one can decide whether the union of the clause falsification events has a pointwise inclusion–exclusion formula using intersections of at most D clauses, find the coefficients if they exist, and count models. A hidden tree with d positive counts guarantees D ≤ 2d. Independent unit clauses on a path show **2d is sharp** for this representation. The degree parameter counts *clause events*. Clauses themselves can have arbitrary literal width.

## How the algorithm discovers the coefficients

Write Aᵢ for the set of assignments falsifying clause i. Each Aᵢ is a Boolean subcube or the empty set. For nonempty S of size at most D, form Bₛ = ⋂ᵢ∈ₛ Aᵢ. Drop empty cubes and merge identical cubes. Seek a rational linear combination g of their indicators that equals 1 on every nonsatisfying assignment. Every feature vanishes on every satisfying assignment.

For each nonempty intersection J of at most D+1 clauses, impose the equation

$$\sum_S a_S\,|J\cap B_S|=|J|.$$

All matrix entries come from at most 2D+1 original clauses. Conflicting signed assignments give volume zero. Otherwise fixing b distinct variables gives volume 2ⁿ⁻ᵇ. These operations use the input literals and integer arithmetic.

**Completeness of the equations.** Fix any clause event A and put r = 1−g. The tests on A and on each A∩Bₛ say that the sums of r on these sets vanish. Hence

$$\sum_{x\in A}r(x)^2
=\sum_{x\in A}r(x)-\sum_S a_S\sum_{x\in A\cap B_S}r(x)=0.$$

Every summand is nonnegative, so g equals 1 on every point of A. Conversely a pointwise formula satisfies all the equations. An inconsistent linear system rules out every degree-D formula of this kind. A consistent one gives the model count 2ⁿ−Σₛaₛ|Bₛ|. To produce a model, restrict the same signed sum to each successive zero-bit branch. Choose that branch if it contains a model and the one-bit branch otherwise. This reuses the discovered coefficients throughout.

**Bit cost.** Let B and T be the number of distinct nonempty cubes at degrees through D and D+1. They are bounded by Σⱼ₌₁ᴰ binom(m,j) and Σⱼ₌₁ᴰ⁺¹ binom(m,j), respectively, with higher binomial terms interpreted as zero. Construction of the features costs polynomially many intersections for fixed D. The linear system has T equations in B unknowns. The implementation streams equations, keeps at most B pivot rows, and uses O(T(B+1)²) rational operations. Entries have at most n+1 bits. Elimination coefficients are ratios of minors, whose bit lengths are O((B+1)(n+log(B+1))) by Hadamard's bound. Exact rational arithmetic, feature storage, input renumbering and n restricted counts thus all have polynomial bit cost for fixed D. The public entry point `solve_cnf(clauses, degree)` assigns dense indices to occurring variables and returns a model using the original identifiers. The low-level API additionally returns certificate coefficients and can count over a larger, explicitly supplied universe of n variables. Degree is an exponent parameter. General use at D=m can require exponentially many columns.

## Why a hidden tree suffices, and why twice the number of levels is optimal

Let xᵢ be the zero-or-one indicator that clause i is false. After rooting a tree, a falsified vertex starts a component exactly when it is the root or its parent is satisfied. Its total component count is the quadratic polynomial

$$c=x_{\rm root}+\sum_{i\ne{\rm root}}x_i(1-x_{{\rm parent}(i)}).$$

Write λ₁,…,λd for its distinct positive values and L for their product. Then L−∏ⱼ(λⱼ−c) vanishes on models, equals L on nonsatisfying rows, has zero constant term, and has degree at most 2d. On Boolean flags repeated factors collapse, so its monomials give nonempty intersections of at most 2d clause events. Division by L yields precisely a solution to the discoverable system above. The algorithm can try increasing degrees or use a chosen cutoff. Acceptance certifies an answer even when the hidden-tree hypothesis is unknown.

For sharpness take 2d unit clauses on different variables in path order. Every Boolean pattern of falsified clauses is realizable. The positive component counts are exactly 1 through d. On a complete Boolean trace the coefficient of every nonempty subset S in a pointwise union identity must be (−1)^{|S|+1}. This follows by summing coefficients on the subsets of each active set and applying induction. In particular the coefficient of the full 2d-set is nonzero. This is also a direct obstruction to a fixed-degree treatment of all CNFs in their original encoding. The independent-unit instances themselves have an immediate SAT algorithm.

## A separate sharp bound on tree representations

For a nonempty nontautological, subsumption-free width-w CNF, if some clause tree has **at most k components on every row**, then

$$m \leq k\,2^{w+1}-1.$$

The bound is attained for every w,k ≥ 1. A satisfiable formula has strict inequality. For k=1 the satisfiable maximum is exactly 2^{w+1}−2. In particular the two maxima at width three are 15 and 14. Subsumption-free means that distinct clauses do not contain one another as literal sets. Semantic minimality is a stronger condition.

**Upper bound.** A uniform assignment falsifies the root with probability at least 2⁻ʷ. For every other clause, choose a parent literal missing from the child. Conditional on the child being false, that literal is either forced true or is true with probability one half. Thus each other vertex starts a component with probability at least 2⁻⁽ʷ⁺¹⁾. Summing gives E[c] ≥ (m+1)2⁻⁽ʷ⁺¹⁾. A model has c=0, making E[c] < k in the satisfiable case.

**Construction.** Take a complete binary tree to depth w, with anchor bits a₀,…,a𝑤₋₁ and address bits b₀,…,b𝑤₋₁. At depth j, the clause for prefix u is false precisely when b₀,…,bⱼ₋₁ match u and all aᵢ with i≥j are zero. Each clause has width w. The false vertices form a nonempty suffix of one branch. All clauses are distinct, and removing a leaf leaves a satisfiable formula with one fewer clause.

To add exactly one component on **every** assignment, keep the original 2ʷ leaves as attachment points. At a leaf with address (u,p), retain the first w−1 address conditions u. Attach two children testing these conditions and opposite signs of a new bit zₚ. Use two fresh variables for the entire round, one for each p. On any row exactly one prefix u matches. For each p one child is false, and exactly one of their two parents is false. Thus one child extends a component and the other starts a new one. Each round adds 2ʷ⁺¹ distinct equal-width clauses. Performing k−1 rounds attains k·2ʷ⁺¹−1. Fresh-variable indices and polarities separate rounds and ports.

## Implementation and adversarial checks

- The host-free counter and model finder use rational elimination. A second implementation detects positive component levels on a supplied tree using exact moments. It tests a proposed polynomial Q by summing cQ(c)², then uses Q(c)/Q(0) as the model indicator. A third routine discovers an exact connected host, when one exists, by maximizing the sum of pairwise intersections over spanning trees and testing all pairs of component starts for a collision. [Automatic discovery](clause_span.py) · [Tree algorithms](clause_trees.py)
- The spanning-tree test is complete for connected rows. For any tree the total number of components over all assignments equals Σᵢ|Aᵢ|−Σₑ|Aᵢ∩Aⱼ| and bounds the size of the union from above. If any tree attains equality, every maximum-weight tree does. The implementation uses O(m²) subcube calculations for construction and verification. The explicit tree moment algorithm takes degree through 2d+1 in c. Its signed subcube expansion has at most (2m)ʲ terms before combining equal cubes at order j.
- On all 48 normalized families over two variables, the tree finder agreed with a search through every labeled tree. On 100 seeded formulas it also handled repetitions, tautologies and empty clauses. The coefficient solver agreed with the pointwise truth-table feasibility problem on all 444 formula-and-degree pairs. Direct evaluation checked each returned indicator at every row. Twelve extremal families passed connected-component searches over all 7,140 of their assignment rows. [Test source](check_clause_trees.py) · [Experiment output](tree-experiments.json)
- A width‑3 example with 42 clauses on 16 variables has 32,768 models, 16,384 rows with four components, and 16,384 with seven. The supplied-tree solver recovered both positive levels. The automatic solver recovered a four-term degree-one certificate and a model using just the clauses. The construction combines two guarded copies of the extremal family. Increasing their round counts yields satisfiable width‑3 examples of unbounded size with two positive levels on the exhibited tree. The sharp capacity bound forces the maximum component count on **every** tree to grow with the formula size. This separates the two parameters. The guards make this a structural separation example, rather than a benchmark for SAT solver speed.
- On the ordinary ten-clause 2-CNF for two-coloring a five-cycle, the equations rejected degree one and certified unsatisfiability at degree two. For 1 through 6 independent units, the solver rejected the degree just below the number of variables, then found all 2ᵐ−1 nonzero coefficients at full degree.

## Verification and novelty

The pinned Lean sources prove the sharp capacity inequality, the extremal construction's size, width, clause antichain and component counts, the integer-scaled local equations criterion, the model-count identities, the degree lift down to actual clause intersections, and full-trace coefficient uniqueness. The Python implementations of rational elimination, spanning-tree selection and bit-mask arithmetic are tested independently of the proof. Reproduce from the workspace with the following commands. [Tree proofs](ClauseTrees.lean) · [Linear certificate proofs](ClauseSpan.lean) · [Kernel and axiom output](../verification.json)

    python verify.py
    python -B research/check_clause_trees.py

Small inclusion–exclusion formulas for a set system, including the characterization through linear equations on an explicit Venn diagram, are established. Amano et al. proved an information-determination theorem for bounded literal width. Hunter proved the spanning-tree union bound. Prior work on signed subcube sums, hitting formulas, and bounded-degree algebraic proof search also uses overlapping ingredients. [Goaoc et al.](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/simplifying-inclusionexclusion-formulas/BB9463B894400E46ED8D62881D2F017F) · [Amano et al.](https://doi.org/10.1016/S0020-0190(03)00259-X) · [Hunter](https://doi.org/10.1017/S0021900200104164) · [Filmus et al., subcube sums](https://eccc.weizmann.ac.il/report/2020/082/) · [Filmus et al., hitting formulas](https://arxiv.org/abs/2302.06241)

The candidate contributions are the sharp hidden-tree-to-degree theorem with coefficient discovery from the CNF alone, and the exact extremal clause count for bounded tree components. The searches of primary literature, the pinned Mathlib and the proof repository did not locate either combined statement. The linear algebra, square-residual argument, support-tree objective, and full-trace Möbius coefficients have established antecedents. Independent novelty review remains open.

This gives the project's constructive SAT track a deterministic, testable sufficient condition. The exact degree lower bound already excludes a universal constant for clauses as supplied. Extending the method to general SAT would require an efficiently constructible representation or a different algorithm for the instances it rejects, including a polynomial bound on the entire transformation. [Equality-side program](https://pequalnp.com/program#p_eq_np_search)
