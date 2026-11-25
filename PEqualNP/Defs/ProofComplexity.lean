import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Definitions of the proof complexity program

The ruling behind this file is `ProofComplexity/README.md`. The pinned Mathlib has no
propositional proof system with a notion of proof length, so the thin layer is here:

* literals, clauses, sets of clauses (CNF formulas) and satisfaction by an assignment;
* the resolution rule, resolution derivations and refutations, with length and width read
  off the list of clauses;
* the pigeonhole formulas `PHP m n`.

Variables are the elements of an arbitrary type `V`. An assignment is a function `V → Bool`.
-/

namespace PEqualNP.ProofComplexity

/-- A literal: a variable with a sign. `(v, true)` is the variable `v`, `(v, false)` is its
negation. -/
abbrev Literal (V : Type) : Type := V × Bool

/-- A clause: a finite set of literals, read as their disjunction. The empty clause is `∅`. -/
abbrev Clause (V : Type) : Type := Finset (Literal V)

/-- The assignment `a` satisfies the clause `C`: it makes some literal of `C` true. The empty
clause is satisfied by no assignment. -/
def ClauseSat {V : Type} (a : V → Bool) (C : Clause V) : Prop :=
  ∃ l ∈ C, a l.1 = l.2

/-- The assignment `a` satisfies the set of clauses `F` (a CNF formula): it satisfies every
clause of `F`. -/
def Satisfies {V : Type} (a : V → Bool) (F : Set (Clause V)) : Prop :=
  ∀ C ∈ F, ClauseSat a C

/-- Some assignment satisfies every clause of `F`. -/
def Satisfiable {V : Type} (F : Set (Clause V)) : Prop :=
  ∃ a : V → Bool, Satisfies a F

/-- The resolution rule: `R` is the resolvent of `C` and `D` on some variable `v` that occurs
positively in `C` and negatively in `D`. The resolvent is `C` without `v` together with `D`
without the negation of `v`. There is no weakening rule. -/
def IsResolvent {V : Type} [DecidableEq V] (C D R : Clause V) : Prop :=
  ∃ v : V, (v, true) ∈ C ∧ (v, false) ∈ D ∧ R = C.erase (v, true) ∪ D.erase (v, false)

/-- `IsDerivation F π`: the list `π` is a resolution derivation from the clauses `F`, written
NEWEST CLAUSE FIRST. Each clause of the list is a clause of `F`, or the resolvent of two
clauses that stand after it in the list (so were derived before it). The number of lines of
the derivation is `π.length`. -/
inductive IsDerivation {V : Type} [DecidableEq V] (F : Set (Clause V)) :
    List (Clause V) → Prop
  | nil : IsDerivation F []
  | ax {π : List (Clause V)} {C : Clause V} :
      IsDerivation F π → C ∈ F → IsDerivation F (C :: π)
  | res {π : List (Clause V)} {C D R : Clause V} :
      IsDerivation F π → C ∈ π → D ∈ π → IsResolvent C D R → IsDerivation F (R :: π)

/-- A resolution refutation of `F`: a derivation from `F` that contains the empty clause. Its
length is `π.length`; its width is the largest `Finset.card` of a clause in it. -/
def IsRefutation {V : Type} [DecidableEq V] (F : Set (Clause V)) (π : List (Clause V)) : Prop :=
  IsDerivation F π ∧ (∅ : Clause V) ∈ π

/-- The pigeonhole formula with `m` pigeons and `n` holes. The variable `(i, j)` says pigeon
`i` sits in hole `j`. The clauses: for each pigeon `i`, the clause "pigeon `i` sits in some
hole"; for each hole `j` and each two different pigeons `i`, `i'`, the clause "not both `i`
and `i'` sit in `j`". It is unsatisfiable exactly when `m > n`. -/
def PHP (m n : ℕ) : Set (Clause (Fin m × Fin n)) :=
  {C | ∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))} ∪
  {C | ∃ (i i' : Fin m) (j : Fin n), i ≠ i' ∧ C = {((i, j), false), ((i', j), false)}}

end PEqualNP.ProofComplexity
