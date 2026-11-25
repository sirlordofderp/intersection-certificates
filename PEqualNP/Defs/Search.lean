import Mathlib.Computability.Language
import Mathlib.Data.Nat.Bits
import PEqualNP.Defs.ProofComplexity

/-!
# Definitions of the P = NP algorithm search: CNF formulas and SAT

The ruling behind this file is `Search/README.md`. The pinned Mathlib has no CNF formulas and
no satisfiability problem outside the internals of a tactic, so they are defined here, as
plainly as possible.

* A variable is a natural number. A literal is a variable and a polarity: `(i, true)` is the
  variable `i`, `(i, false)` its negation.
* A clause is a list of literals (their disjunction); a CNF formula is a list of clauses
  (their conjunction). The empty clause is false; the empty formula is true.
* An assignment gives every variable a truth value.
* SAT is the language of the binary strings that encode a satisfiable CNF formula, under
  `encodeCNF` below. A string that encodes no formula is not in SAT.
-/

namespace PEqualNP.Search

/-- A literal: a variable (a natural number) and a polarity, `true` for the variable itself,
`false` for its negation. -/
abbrev Literal : Type := ℕ × Bool

/-- A clause: the disjunction of its literals. -/
abbrev Clause : Type := List Literal

/-- A CNF formula: the conjunction of its clauses. -/
abbrev CNF : Type := List Clause

/-- An assignment of a truth value to every variable. -/
abbrev Assignment : Type := ℕ → Bool

/-- The value of a literal under an assignment: true when the variable's value equals the
literal's polarity. -/
def Literal.eval (σ : Assignment) (l : Literal) : Bool :=
  σ l.1 == l.2

/-- The value of a clause: true when some literal of it is true. -/
def Clause.eval (σ : Assignment) (c : Clause) : Bool :=
  c.any (Literal.eval σ)

/-- The value of a CNF formula: true when every clause of it is true. -/
def CNF.eval (σ : Assignment) (φ : CNF) : Bool :=
  φ.all (Clause.eval σ)

/-- A CNF formula is satisfiable when some assignment makes it true. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, CNF.eval σ φ = true

/-- A formula is a k-CNF when every clause has at most `k` literals. -/
def IsKCNF (k : ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, c.length ≤ k

/-- The binary encoding of a literal `(i, b)`. The string is read in pairs of bits: a pair
`[true, d]` is a digit `d`, `[false, true]` ends a literal, `[false, false]` ends a clause. A
literal is its polarity as a digit, then the binary digits of `i` (least significant first, no
leading zeros, so `0` has no digits; `Nat.bits`), then the end-of-literal pair. -/
def encodeLiteral (l : Literal) : List Bool :=
  [true, l.2] ++ (l.1.bits.flatMap fun d => [true, d]) ++ [false, true]

/-- The binary encoding of a clause: its literals in order, then the end-of-clause pair. -/
def encodeClause (c : Clause) : List Bool :=
  c.flatMap encodeLiteral ++ [false, false]

/-- The binary encoding of a CNF formula: its clauses in order. Its length is a constant times
the number of literals and clauses plus the total number of binary digits of the variables,
so it is the usual size of a formula up to a constant factor. -/
def encodeCNF (φ : CNF) : List Bool :=
  φ.flatMap encodeClause

/-- SAT: the binary strings that encode a satisfiable CNF formula. -/
def SAT : Language Bool :=
  {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ}

/-- k-SAT: the binary strings that encode a satisfiable k-CNF formula. -/
def KSAT (k : ℕ) : Language Bool :=
  {x | ∃ φ : CNF, IsKCNF k φ ∧ encodeCNF φ = x ∧ Satisfiable φ}

/-! ## Resolution over parities, Res(lin) over F2

The proof system in which the unsatisfiable runs of a CDCL solver over parities live (candidate 3
of this program). A line is a disjunction of linear equations over F2 on the variables `Fin n`.
Rules: an axiom (a clause of the formula, each literal `(v, b)` read as the equation `v = b`),
resolution on one linear form, and semantic weakening (from one earlier line, any line it
implies). Semantic weakening makes the system at least as strong as the syntactic variants in
the literature, so a lower bound on it is at least as strong. -/

/-- A linear equation over F2: the variables in the set sum to the bit (`true` is 1). -/
abbrev LinEq (n : ℕ) : Type := Finset (Fin n) × Bool

/-- The assignment `a` satisfies the equation `e`: an odd number of the variables of `e` are
true exactly when the right-hand side of `e` is `true`. -/
def LinEq.Holds {n : ℕ} (a : Fin n → Bool) (e : LinEq n) : Prop :=
  (e.1.filter fun i => a i = true).card % 2 = 1 ↔ e.2 = true

/-- A linear clause: the disjunction of its equations. The empty linear clause is false. -/
abbrev LinClause (n : ℕ) : Type := List (LinEq n)

/-- The assignment `a` satisfies the linear clause `C`: it satisfies some equation of `C`. -/
def LinClause.Holds {n : ℕ} (a : Fin n → Bool) (C : LinClause n) : Prop :=
  ∃ e ∈ C, LinEq.Holds a e

/-- `IsResLinDerivation F π`: the list `π` of linear clauses is a Res(lin) derivation from the
clauses `F`, written NEWEST LINE FIRST. Each line is an axiom (it has exactly the equations
`{v} = b` for the literals `(v, b)` of some clause of `F`), or the resolvent of two earlier
lines `e :: C` and `e' :: D` whose first equations have the same variable set and different
right-hand sides (the resolvent is `C ++ D`), or implied by one earlier line. -/
inductive IsResLinDerivation {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    List (LinClause n) → Prop
  | nil : IsResLinDerivation F []
  | ax {π : List (LinClause n)} {L : LinClause n} (C : PEqualNP.ProofComplexity.Clause (Fin n)) :
      IsResLinDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = ({l.1}, l.2)) →
      IsResLinDerivation F (L :: π)
  | res {π : List (LinClause n)} {e e' : LinEq n} {C D : LinClause n} :
      IsResLinDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π → e.1 = e'.1 → e.2 ≠ e'.2 →
      IsResLinDerivation F ((C ++ D) :: π)
  | weaken {π : List (LinClause n)} {C D : LinClause n} :
      IsResLinDerivation F π → C ∈ π → (∀ a : Fin n → Bool, LinClause.Holds a C → LinClause.Holds a D) →
      IsResLinDerivation F (D :: π)

/-- A Res(lin) refutation of `F`: a derivation from `F` containing the empty linear clause. Its
size is its number of lines, `π.length`. -/
def IsResLinRefutation {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (π : List (LinClause n)) : Prop :=
  IsResLinDerivation F π ∧ ([] : LinClause n) ∈ π

end PEqualNP.Search
