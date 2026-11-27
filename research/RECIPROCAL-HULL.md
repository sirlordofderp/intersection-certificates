# Which parity equations hold on every admissible induced subgraph?

Label each vertex of a finite undirected simple graph either 0 or 1. A vertex set is *admissible* if, inside its induced subgraph, each selected vertex has the degree parity written on it. Vertices outside the set impose no conditions. The empty set is admissible.

**Theorem.** The binary span of the incidence vectors of all admissible sets consists exactly of the vectors having an even number of selected 1-labelled vertices in each connected component. If the graph has n vertices and c components containing at least one 1-label, the dimension is n−c.

Thus the connected components tell us *every* affine equation shared by the admissible sets. They also let us produce an actual admissible set meeting a proposed parity condition in polynomial time. The span can contain inadmissible sets. On a three-vertex path labelled 1,0,1, both endpoints together satisfy the component equation, yet their induced degrees are zero. The whole path and the middle singleton are admissible, and their binary sum is the endpoint pair.

## Proof and constructive basis

Write d for the label vector. In an admissible set the 1-labelled selected vertices are exactly its odd-degree vertices. The degree-sum formula makes their number even inside each original component.

For the converse, suppose a weight vector a sums to zero on every admissible set. A singleton at any 0-labelled vertex is admissible, so a vanishes there. If a component contains two 1-labelled vertices of different weights, take a closest such pair. A shortest path between them has no chord. An internal 1-labelled vertex would give a closer pair with different weights. All internal vertices are therefore 0-labelled. The path's endpoints have induced degree one, and its internal vertices have degree two. It is admissible, yet its weight is one. This contradiction shows that a is constant on the 1-labelled vertices of each component. These are precisely the linear combinations of the component equations. Finite-dimensional duality gives the claimed span and dimension.

For a constructive basis, include every 0-labelled singleton. From each 1-labelled vertex run breadth-first search through 0-labelled interiors, recording shortest paths when another 1-labelled vertex is reached. Each path is admissible. Modulo the singletons, its vector is the pair of endpoints. Splitting a connecting walk at its 1-labelled vertices shows that the graph of these endpoint pairs connects the 1-labelled vertices in each component. Its edge vectors span their even-parity subspace. Binary elimination on the singletons and path vectors returns n−c independent **actual** admissible sets. There are at most n searches and quadratically many candidate paths. The Python bit-mask implementation, including witness materialization and elimination, uses polynomial time and space.

## A deterministic SAT application

An affine clause is a disjunction of equations over binary parity. Select one normal vector per matched clause so that the selected normals are independent. Maximal transversal augmentation removes a part solvable by ordinary elimination. If there is one unmatched clause, the remaining core has r basis coordinates, r matched clauses, and one extra clause. The matched equations fix a common origin. Translate it to zero so that matched clause i contains the baseline option xᵢ=0. This reduction and the more general randomized SAT algorithm by maximum rank deficiency are in the November 23 preprint by OpenAI Codex and Yichuan Wang. [Primary paper, Lemmas 2–3 and Theorem 1](https://airaxiv.com/papers/pdf/2611.0031/?v=1)

On the slice xᵢ=1, an alternative equation a·x=b can be written as (a+b eᵢ)·x=0. When each row has one effective alternative, write these normals as the rows of N. No effective alternative gives the row eᵢ. An alternative always true on the slice gives the zero row. The matched formula then says

$$x_i (Nx)_i=0\qquad\text{for every }i.$$

If N is symmetric, its off-diagonal entries specify edges and its diagonal specifies the vertex labels. The active coordinates are exactly an admissible set. For any extra disjunction of parity equations, evaluate it on the origin and the basis of actual models constructed above. If a linear test takes both values anywhere on the models, at least one basis vector changes its value from the origin. This gives deterministic SAT and UNSAT decisions, with a checked assignment on SAT. The recognizer tests reciprocity in the coordinates supplied by its transversal. Finding a better transversal is a separate problem.

This result handles examples with an unbounded number of independent cyclic dependencies. For instance, the implications xᵢ⇒xⱼ and xⱼ⇒xᵢ on each of t disjoint pairs force equality within pairs. In either order inside every pair, the earlier equation depends on its later partner. The ordered method needs t independent guessed parities for this fixed coordinate basis. The graph theorem reads off the span directly. [Ordered method](ORDERED-AFFINE.md)

## The directed problem and a determinant criterion

For arbitrary N, the matrix criterion still makes sense. A directed cycle with rows eᵢ+eᵢ₊₁ requires that the support of any nonzero model contain the entire cycle. In dimension three the only models are 000 and 111. The component parity rule for the undirected case fails here. In any dimension an odd probe x₁=1 on this family can require the full support.

There is an exact algebraic reduction for arbitrary, possibly nonsymmetric N. For a matrix M let F(M) be the family of index sets S such that the principal matrix M[S] is invertible over the binary field. For a binary probe a, the following are equivalent.

1. Every model of xᵢ(Nx)ᵢ=0 satisfies a·x=0.
2. For every i, F(N+eᵢaᵀ) is contained in F(N).

**Proof.** If containment fails on S, select a nonzero vector y in the kernel of N[S]. The updated principal matrix is invertible, so a restricted to S has nonzero product with y. Pad y with zeros. Each active coordinate then satisfies its own row and a·y=1.

Conversely, choose a model of minimum support S among those with a·x=1. Its restriction is the all-ones vector in the kernel of N[S]. Any second independent kernel vector supplies a nonzero kernel vector z of even probe value, by adding the all-ones vector if necessary. Adding z to the chosen solution gives a smaller odd-probe model. Thus the kernel is one-dimensional. Select i in S so that deleting row i leaves rank |S|−1. The other rows span the original row space, whereas a restricted to S is outside that space. Adding aᵀ to row i makes the minor invertible. This proves the equivalence.

The same argument permits several independent row choices per clause. Let vᵢⱼ be the normalized row for option j, including the baseline row if needed, and form a matrix with row i equal to Σⱼ zᵢⱼ vᵢⱼ plus tᵢeᵢ. In its determinant, the coefficient of the monomial choosing t outside S and one option weight per row inside S is precisely the corresponding principal minor. Make one new polynomial per row i by replacing every vᵢⱼ in that row with vᵢⱼ+a. The model invariant is equivalent to containment of each updated monomial support in the original support. Every indeterminate contributes a rank-one coefficient matrix. A polynomial-time deterministic test for **this particular inclusion** would decide the whole one-unmatched-clause case, by testing each alternative of its extra clause after translation.

The decision test would also yield a witness. For an attainable odd probe, visit each coordinate once and test whether the probe remains attainable with that coordinate zero. Setting it to zero satisfies its baseline clause, so delete that row and coordinate and restrict all other rows and the probe. Keep the deletion whenever the answer is yes. Every coordinate still present must be one in every surviving odd-probe model. Setting those coordinates to one and the deleted coordinates to zero recovers a model with at most r additional tests.

Equality of two rank-one-generated symbolic determinants has a deterministic polynomial-time test. Over the binary field that tests equality of their monomial supports. Proper containment really occurs here. For N=[1] and a=[1], the probe is invariant and the update loses the nonempty principal minor. The equality algorithm by itself therefore leaves an algorithmic question. The experiments also record a satisfiable, non-tautological example on which tying option weights across rows cancels all terms. [Chatterjee, Ghosh, Gurjar and Raj, Theorem 1.3](https://www.cse.iitb.ac.in/~rgurjar/papers/PMESTOC25.pdf) · [Cancellation example](affine-shortfall-experiments.json)

## Evidence, prior work, and reproduction

The graph object already appears in extremal combinatorics under the name ℓ-admissible induced subgraph. Ai and coauthors and Guo and coauthors study how *large* a single such set can be. Our question asks which binary linear equations hold on their entire family. The degree-sum argument and the linear algebra are classical. The exact hull classification, its constructive basis, and its use for deterministic affine SAT are the contribution proposed for review. The literature search located no earlier statement of that classification. Historical priority remains unconfirmed. [Ai et al.](https://arxiv.org/abs/2509.01428) · [Guo et al.](https://arxiv.org/abs/2608.02339)

Lean checks the full dual characterization, including the shortest-path converse, and the odd-probe equivalence in `invariant_iff` and `odd_probe_iff`. The primal dimension follows by finite-dimensional duality. The nonsymmetric determinant reduction above has a written proof and exhaustive small tests. The executable solvers were differentially tested. [Lean source](ReciprocalHull.lean) · [Deterministic solver](reciprocal_affine.py) · [Experiment source](check_reciprocal_affine.py)

Run `python -B research/check_reciprocal_affine.py` from the repository root. It checks all 33,867 symmetric binary matrices of orders zero through five, covering 254,254 admissible supports. It also checks 400 signed solver instances, every binary matrix and probe through order three (4,165 pairs), and 1,024 probes on multi-option directed systems. The complete repository check is `python verify.py --fetch-cache`. [Recorded output](reciprocal-experiments.json) · [Verification record](../verification.json)
