# Sharp intersection orders for counting and recognition

## Setting

Let A₁,…,Aₘ be events in a finite universe of known size N. A point gives a vector x∈{0,1}ᵐ. Let μ(x) be its multiplicity. For a set of indices S, write xₛ=∏ᵢ∈ₛxᵢ and Mₛ=Σₓ μ(x)xₛ. The order-k information consists of every **labelled** Mₛ with |S|≤k, including M∅=N. An algorithm can request these numbers adaptively. The results concern how large an individual S must be. The information model makes no assumptions about how the oracle obtains Mₛ.

A degree-d identity is a rational polynomial g with zero constant term, degree at most d, and g(x)=1 on each nonzero pattern present in the population. Because xᵢ²=xᵢ, this is exactly a rational linear combination of nonempty intersections. Equivalently, P=1−g is 1 at the origin and vanishes on all present nonzero patterns. The normalization at the origin is part of the problem even when no point has that pattern. Lean clears rational denominators and uses P(0)=L≠0. Zero-multiplicity rows impose no other restrictions.

## Two tasks with different thresholds

**Theorem.** For each d≥1, the sharp worst-case order for computing μ(0) under the promise of a degree-d identity is 2d. The sharp worst-case order for recognizing the existence of a degree-d identity is 2d+1. When m is smaller, data through order m already specify the whole population. The lower bounds choose m=2d and m=2d+1 respectively.

**Why 2d determines the answer.** Consider two populations with the same order-2d moments and possibly different normalized certificates P,Q. The polynomial PQ has degree at most 2d, so its sum is the same on both populations. On the first population P vanishes on nonzero rows. On the second Q does. Its sum in each case is exactly the mass of the origin. [Lean theorem `count_transfer`](IntersectionOrder.lean)

**How to compute it.** Index a dictionary by all nonempty S with |S|≤d. Form the Gram matrix Gₛₜ=Mₛ∪ₜ and the vector bₛ=Mₛ. Solve Ga=b over the rationals, setting free variables to zero if necessary. These are the normal equations for projecting the union indicator onto the span of the dictionary columns. They are consistent, since b is the inner product vector of the union indicator against those columns. Equivalently, every vector in the kernel of G is a zero combination of columns on all present points and is orthogonal to b. All solutions give the same function on present rows. Under the promise this function is the union indicator. Return N−bᵀa.

**How to verify the promise.** Write g=Σaₛxₛ, r=1−g, and h=Σxᵢ. Compute R=Σₓμ(x)h(x)r(x)² by expansion using order 2d+1. Every summand is nonnegative. Hence R=0 exactly when r vanishes on all present nonzero rows. If R>0, the least-squares solution failed, which rules out every degree-d identity. In particular equal order-(2d+1) data transfer the validity of each individual degree-d certificate between populations. [Lean theorem `certificate_transfer`](IntersectionOrder.lean) · [Implementation](intersection_order.py)

More generally, a known polynomial H of degree t, nonnegative on all Boolean rows, can mark an arbitrary region by H>0. Order 2d+t transfers the property that a degree-d residual vanishes everywhere in that region having positive mass. This separates the complexity of marking the region from that of the residual being verified. [Lean theorem `detector_transfer`](IntersectionOrder.lean)

## Matching lower bounds

Use uniform unit multiplicity on either the even or odd parity half of the m-dimensional cube. Every specified proper subset of coordinates leaves a free bit. Flipping it pairs even completions with odd completions and preserves all specified bits. Thus **every** proper labelled intersection agrees, including the universe size.

- **Promised counting.** Put m=2d. On the even half the positive Hamming weights are 2,4,…,2d. On the odd half they are 1,3,…,2d−1. On either half multiply the d factors (1−|x|/j) over its positive weights j. This is a normalized degree-d certificate. The even population has one origin and the odd population has none. They are indistinguishable through order 2d−1.
- **Recognition.** Put m=2d+1. The even population again has a degree-d certificate. If the odd population had one, its normalized P would vanish on every odd row. P² has degree at most 2d, so its sum on the even half would also be zero. The origin contributes one to that sum, and the remaining summands are nonnegative. This is a contradiction.

Both witnesses can have uncovered points. Append identical all-zero rows to both populations. No positive-order moment or degree constraint changes, and both universe sizes increase equally. The witnesses also have succinct realizations: use m−1 independent binary variables as the first event flags and their parity, optionally complemented, for the last. Requiring a common guard bit for all events doubles the universe and adds a block of uncovered assignments. This uses affine falsification events over GF(2). Sharpness specifically for single signed CNF clauses under a width bound is a separate question. [Lean theorems `proper_moments`, `counting_sharp`, and `recognition_sharp`](IntersectionOrder.lean)

## An integer answer after an exact identity fails

Let U be the union size, L=bᵀa, and δ=U−L. The normal equations give Σμrg=0, so δ is precisely Σₓ≠₀μ(x)r(x)². On a present nonzero row 1≤h≤m. Consequently δ≤R≤mδ. For m>0 this gives the interval

$$
\max(0,\lceil N-L-R\rceil)\ \le\ \mu(0)\ \le\
\min(N,\lfloor N-L-R/m\rfloor).
$$

For two independent event flags, with all four patterns present once, the degree-one projection has both coefficients 2/3. Its uncovered estimate is 4/3 and R=4/9. The interval contains just **one** integer. Thus the algorithm certifies the correct count although no pointwise linear identity exists. For the empty family the answer is N directly. [Lean theorems `projection_gap` and `weighted_gap_bounds`](IntersectionOrder.lean)

## Changing the representation

Replace each event flag by a disjoint block of t≥1 raw bits. Encode true by the block parity of the all-ones word, and false by the opposite parity. Every raw row receives the multiplicity of its decoded event pattern. A raw conjunction requests one-bits in a set Qᵢ in each block. Let F be the indices of the blocks requested in full. A partially requested block has exactly 2^{t−|Qᵢ|−1} completions for either decoded value. A fully requested block must encode true and has one completion. The labelled intersection size is therefore

$$
M^\mathrm{raw}_Q =
2^{\sum_{i\notin F}(t-|Q_i|-1)}\,M_F.
$$

It follows in both directions that two encoded populations agree through raw order k **if and only if** the original populations agree through order ⌊k/t⌋. For the reverse direction, request only full blocks and divide out the known, positive multiplicity. The number of raw rows decoding to the all-zero macro pattern is 2^{(t−1)m}μ(0). Thus the sharp raw orders for the *decoded* counting and recognition tasks are 2dt and (2d+1)t. These statements assume the block partition is given. They do not use a search over encodings. [Lean theorems `block_counts_rows`, `block_order_iff`, `block_counting_sharp`, and `block_recognition_sharp`](IntersectionOrder.lean)

## Complexity and experiments

Let B=Σⱼ₌₁ᵈ binom(m,j), treating terms with j>m as zero. Building the Gram system takes O(B²) oracle calls. Exact elimination uses O(B³) rational operations and O(B²) rational working entries. The validation loop uses O(m(B+1)²) oracle calls and arithmetic operations. Queries can be cached by their union of indices. The integers in the Gram system have O(log(N+1)) bits. Determinant bounds give O((B+1)(log(N+1)+log(B+1))) bits for reduced elimination entries up to constant factors. Certificate evaluation and rational sums also have polynomial bit cost. These bounds are polynomial for fixed d. In particular N can be exponential in the length of an implicit input; the assumption required is a polynomial-time exact intersection oracle with polynomial-length answers.

The supplied affine oracle takes a conjunction of binary linear equations for each event. For an intersection it combines the selected equations, returns zero if they conflict, and otherwise returns 2^{n−rank}. With u combined equations, straightforward binary elimination uses O(un²) bit operations up to bookkeeping for variable indices. The dense n-variable representation is explicit. Ordinary clause falsification fixes individual variable bits, and a clause containing disjunctions of parity predicates has an affine falsification event. The solver operates on these systems without enumerating their assignments.

The tests compare the oracle algorithm against the full pointwise linear system on 1,178 population-and-degree cases. In 182 cases the integer interval closed even though the short identity failed. The suite also checks 12 sharp parity pairs, 408 raw-block moments, and two guarded systems using 160 variables. The latter have identical labelled intersections through order five but different counts. Independent rank calculations give 2¹⁵⁹+2¹⁵⁴ and 2¹⁵⁹ uncovered assignments. [Experiments](check_intersection_order.py) · [Recorded results](order-experiments.json)

## What is established and what needs review

Pointwise inclusion–exclusion vectors and their equations on an explicit Venn diagram are established. Pairwise projection bounds for a union belong to the Gallot–Kounias line of work. Linear programming from intersection data, finite moment matrices, and parity-based indistinguishability all have substantial prior literature. Amano et al. give a different information threshold for bounded-width CNF clauses. Their parameter is clause width, whereas d here is the degree of an identity on the realized membership patterns. [Goaoc et al.](https://doi.org/10.1017/S096354831400042X) · [Kounias](https://doi.org/10.1214/aoms/1177698049) · [Prékopa](https://doi.org/10.1287/opre.38.2.227) · [Laurent and Mourrain](https://arxiv.org/abs/0812.2563) · [Amano et al.](https://doi.org/10.1016/S0020-0190(03)00259-X)

The proposed contribution is the paired sharp classification for computing under the promise and recognizing the promise, with explicit all-degree witnesses, a change-of-representation theorem, and reproducible formal proofs. A targeted comparison did not locate these two thresholds stated together for this problem. Historical priority is provisional. The square test, the Gram bound, and parity masking are ingredients with known precedents. The Lean kernel checks the information and residual statements; the implementation and its bit-complexity analysis are separate from that kernel verification.
