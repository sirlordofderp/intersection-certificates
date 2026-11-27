import AffineShortfall
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fintype.Option

/-! Representative assignments for affine-clause extensions. -/
namespace OrderedAffine

open scoped BigOperators
open AffineShortfall (Bit)

section Preservation
variable {V W : Type*} [AddCommGroup V] [Module Bit V] [AddCommGroup W] [Module Bit W]

/-- Every realizable conjunction of d affine tests also has a retained witness. -/
def Hits (d : ℕ) (S B : Set V) : Prop :=
  ∀ q : Fin d → V →ᵃ[Bit] Bit, ∀ x ∈ S, (∀ i, q i x = 1) →
    ∃ y ∈ B, ∀ i, q i y = 1

def successors {I : Type*} (f : I → V →ᵃ[Bit] W) (S : Set V) : Set W :=
  {y | ∃ i, ∃ x ∈ S, f i x = y}

theorem hits_successors {I : Type*} {d : ℕ} {S B : Set V} (h : Hits d S B)
    (f : I → V →ᵃ[Bit] W) : Hits d (successors f S) (successors f B) := by
  rintro q _ ⟨i, x, hx, rfl⟩ hq
  obtain ⟨y, hy, hp⟩ := h (fun j => (q j).comp (f i)) x hx hq
  exact ⟨f i y, ⟨i, y, hy, rfl⟩, hp⟩

/-- Spending h tests on closing guessed parities leaves k tests for the query. -/
theorem hits_closure {k h : ℕ} {S B : Set V} (hh : Hits (k + h) S B)
    (close : Fin h → V →ᵃ[Bit] Bit) :
    Hits k {x ∈ S | ∀ j, close j x = 1} {x ∈ B | ∀ j, close j x = 1} := by
  intro q x hx hq
  let both : Fin (k + h) → V →ᵃ[Bit] Bit := Fin.append q close
  have hall : ∀ j, both j x = 1 := Fin.addCases (fun i => by simpa [both] using hq i)
    (fun i => by simpa [both] using hx.2 i)
  obtain ⟨y, hy, hxy⟩ := hh both x hx.1 hall
  exact ⟨y, ⟨hy, fun j => by simpa [both] using hxy (Fin.natAdd k j)⟩,
    fun i => by simpa [both] using hxy (Fin.castAdd h i)⟩

theorem hits_clauses {k : ℕ} {S B : Set V} (h : Hits k S B)
    (C : Fin k → Set (V →ᵃ[Bit] Bit)) (x : V) (hx : x ∈ S)
    (hc : ∀ i, ∃ q ∈ C i, q x = 1) : ∃ y ∈ B, ∀ i, ∃ q ∈ C i, q y = 1 := by
  choose q hq hqx using hc
  obtain ⟨y, hy, hp⟩ := h q x hx hqx
  exact ⟨y, hy, fun i => ⟨q i, hq i, hp i⟩⟩

/-- Spanning lifted evaluation vectors retains witnesses for every query whose
truth indicator is a linear functional of the lift. -/
theorem feature_pruning {X E : Type*} [AddCommGroup E] [Module Bit E]
    {S B : Set X} (φ : X → E) (hspan : ∀ x ∈ S, φ x ∈ Submodule.span Bit (φ '' B))
    (test : E →ₗ[Bit] Bit) {x : X} (hx : x ∈ S) (ht : test (φ x) = 1) :
    ∃ y ∈ B, test (φ y) = 1 := by
  by_contra! h
  have hker : Submodule.span Bit (φ '' B) ≤ LinearMap.ker test := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    exact (AffineShortfall.bit_eq_zero_or_one _).resolve_right (h y hy)
  have hz : test (φ x) = 0 := hker (hspan x hx)
  exact zero_ne_one (hz.symm.trans ht)

end Preservation

/-- A pivot-free option permits the opposite of the baseline bit precisely
when that option is true. Both possible updates are affine in its truth bit. -/
theorem free_pivot (base truth value : Bit) :
    (value = base ∨ truth = 1) ↔ (value = base ∨ value = base + truth) := by
  exact (by decide : ∀ b t v : Bit, (v = b ∨ t = 1) ↔ (v = b ∨ v = b + t)) base truth value

abbrev Blocks (k b : ℕ) := Fin k → Option (Fin b)
def encode {b : ℕ} (p : Option (Fin b)) (j : Fin b) : Bit := if p = some j then 1 else 0

/-- An occupied position is identified by its bit. The empty block is
identified by parity zero on the entire block. -/
def selector {b : ℕ} (p : Option (Fin b)) (x : Fin b → Bit) : Bit :=
  match p with
  | none => 1 - ∑ j, x j
  | some j => x j

theorem selector_eq_one_iff {b : ℕ} (p q : Option (Fin b)) :
    selector p (encode q) = 1 ↔ p = q := by
  cases p <;> cases q <;> simp [selector, encode, eq_comm]

theorem block_query_unique {k b : ℕ} (p q : Blocks k b) :
    (∀ i, selector (p i) (encode (q i)) = 1) ↔ p = q := by
  simp only [selector_eq_one_iff, funext_iff]

/-- These k single-equation queries already force every one of (b+1)^k
actual models to be present in a reusable witness set. -/
theorem block_all_required {k b : ℕ} (B : Finset (Blocks k b))
    (h : ∀ p : Blocks k b, ∃ q ∈ B, ∀ i, selector (p i) (encode (q i)) = 1) :
    B.card = (b + 1)^k := by
  classical
  have full : B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    obtain ⟨q, hq, hp⟩ := h p
    exact (block_query_unique p q).mp hp ▸ hq
  simp [full, Blocks]

end OrderedAffine
