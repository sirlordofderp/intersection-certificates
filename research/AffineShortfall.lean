import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Field

/-! Isolation of a satisfying assignment by mixing affine tests within each clause. -/
namespace AffineShortfall

open Matrix
open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Vec (n : ℕ) := Fin n → Bit
abbrev Test (n : ℕ) := Vec n × Bit

def eval {n : ℕ} (f : Test n) (x : Vec n) : Bit := f.1 ⬝ᵥ x + f.2

theorem eval_add {n : ℕ} (f g : Test n) (x : Vec n) :
    eval (f + g) x = eval f x + eval g x := by
  simp [eval, add_dotProduct]
  abel

theorem bit_eq_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a

def Mixed {n : ℕ} (C : Set (Test n)) (f : Test n) : Prop :=
  f ∈ C ∨ ∃ u ∈ C, ∃ v ∈ C, f = u + v

theorem mixed_true {n : ℕ} {C : Set (Test n)} {f : Test n} {x : Vec n}
    (hf : Mixed C f) (h : eval f x = 1) : ∃ u ∈ C, eval u x = 1 := by
  rcases hf with hf | ⟨u, hu, v, hv, rfl⟩
  · exact ⟨f, hf, h⟩
  · rw [eval_add] at h
    rcases bit_eq_zero_or_one (eval u x) with hz | ho
    · exact ⟨v, hv, by simpa [hz] using h⟩
    · exact ⟨u, hu, ho⟩

def slopes {n : ℕ} (f : Fin n → Test n) : Matrix (Fin n) (Fin n) Bit :=
  fun i => (f i).1

theorem slopes_update {n : ℕ} (f : Fin n → Test n) (i : Fin n) (v : Test n) :
    slopes (Function.update f i v) = (slopes f).updateRow i v.1 := by
  ext j k
  by_cases h : j = i <;> simp [slopes, Matrix.updateRow, Function.update, h]

/-- At a model, one or two original tests per matched clause suffice to select
true affine forms whose slopes still constitute a basis. -/
theorem model_basis {n : ℕ} (C : Fin n → Set (Test n)) (x : Vec n)
    (base : Fin n → Test n) (hb : ∀ i, base i ∈ C i)
    (hd : (slopes base).det ≠ 0) (hx : ∀ i, ∃ u ∈ C i, eval u x = 1) :
    ∃ f : Fin n → Test n, (slopes f).det ≠ 0 ∧
      ∀ i, Mixed (C i) (f i) ∧ eval (f i) x = 1 := by
  classical
  suffices h : ∀ s : Finset (Fin n), ∃ f : Fin n → Test n, (slopes f).det ≠ 0 ∧
      (∀ i ∈ s, Mixed (C i) (f i) ∧ eval (f i) x = 1) ∧
      ∀ i ∉ s, f i = base i by
    obtain ⟨f, hf, hs, _⟩ := h Finset.univ
    exact ⟨f, hf, fun i => hs i (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨base, hd, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨f, hf, hs, hout⟩ := ih
    have hfi : f i ∈ C i := hout i hi ▸ hb i
    have step : ∃ v, Mixed (C i) v ∧ eval v x = 1 ∧
        ((slopes f).updateRow i v.1).det ≠ 0 := by
      rcases bit_eq_zero_or_one (eval (f i) x) with hz | ho
      · obtain ⟨u, hu, hux⟩ := hx i
        by_cases hdu : ((slopes f).updateRow i u.1).det = 0
        · refine ⟨f i + u, Or.inr ⟨f i, hfi, u, hu, rfl⟩, by simp [eval_add, hz, hux], ?_⟩
          change ((slopes f).updateRow i ((slopes f) i + u.1)).det ≠ 0
          simpa [Matrix.det_updateRow_add, hdu] using hf
        · exact ⟨u, Or.inl hu, hux, hdu⟩
      · exact ⟨f i, Or.inl hfi, ho, by change ((slopes f).updateRow i ((slopes f) i)).det ≠ 0; simpa⟩
    obtain ⟨v, hv, hvx, hvd⟩ := step
    refine ⟨Function.update f i v, by rwa [slopes_update], ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using And.intro hv hvx
      · have hji : j ≠ i := fun e => hi (e ▸ hj)
        simpa [Function.update_of_ne hji] using hs j hj
    · intro j hj
      have hji : j ≠ i := fun e => hj (e ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne hji]
      exact hout j (fun h => hj (Finset.mem_insert_of_mem h))

theorem basis_unique {n : ℕ} {f : Fin n → Test n} {x y : Vec n}
    (hd : (slopes f).det ≠ 0) (hx : ∀ i, eval (f i) x = 1)
    (hy : ∀ i, eval (f i) y = 1) : y = x := by
  apply Matrix.mulVec_injective_of_det_ne_zero hd
  funext i
  exact add_right_cancel ((hy i).trans (hx i).symm)

/-- The moment detects a model even with an arbitrary number of surplus
clauses. Matched choices may be binary sums; surplus choices are original. -/
theorem sat_iff_nonzero_moment {n k : ℕ} (C : Fin n → Set (Test n))
    (D : Fin k → Set (Test n)) (base : Fin n → Test n) (hb : ∀ i, base i ∈ C i)
    (hd : (slopes base).det ≠ 0) :
    (∃ x, (∀ i, ∃ u ∈ C i, eval u x = 1) ∧ (∀ j, ∃ u ∈ D j, eval u x = 1)) ↔
    ∃ f : Fin n → Test n, ∃ g : Fin k → Test n,
      (∀ i, Mixed (C i) (f i)) ∧ (∀ j, g j ∈ D j) ∧
      (∑ y : Vec n, (∏ i, eval (f i) y) * ∏ j, eval (g j) y) ≠ 0 := by
  classical
  constructor
  · rintro ⟨x, hx, hx'⟩
    choose g hg hgx using hx'
    obtain ⟨f, hf, hfx⟩ := model_basis C x base hb hd hx
    refine ⟨f, g, fun i => (hfx i).1, hg, ?_⟩
    rw [Finset.sum_eq_single x]
    · simp [fun i => (hfx i).2, hgx]
    · intro y _ hy
      have h : ∃ i, eval (f i) y = 0 := by
        by_contra! hall
        exact hy (basis_unique hf (fun i => (hfx i).2)
          (fun i => (bit_eq_zero_or_one _).resolve_left (hall i)))
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    · simp
  · rintro ⟨f, g, hf, hg, h⟩
    obtain ⟨x, _, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨hf', hg'⟩ := mul_ne_zero_iff.mp hxy
    have nonzero {l : ℕ} {v : Fin l → Bit} (hprod : ∏ i, v i ≠ 0) :
        ∀ i, v i = 1 := by
      intro i
      apply (bit_eq_zero_or_one _).resolve_left
      intro hz
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    exact ⟨x, fun i => mixed_true (hf i) (nonzero hf' i),
      fun j => ⟨g j, hg j, nonzero hg' j⟩⟩

end AffineShortfall
