import PEqualNP.Defs.Search
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Choose.Sum

namespace ClauseSpan

open Finset PEqualNP.Search

def value {α β : Type*} [DecidableEq α] [Fintype β] (B : β → Finset α)
    (a : β → ℤ) (s : α) : ℤ := ∑ j, if s ∈ B j then a j else 0

/-- Linear tests on A and each A ∩ B_j certify pointwise equality everywhere on A.
    The integer scale L allows arbitrary rational coefficients by clearing denominators. -/
theorem local_equations_iff {α β : Type*} [DecidableEq α] [Fintype β]
    (A : Finset α) (B : β → Finset α) (a : β → ℤ) (L : ℤ) :
    ((∑ s ∈ A, (L - value B a s)) = 0 ∧
      ∀ j, (∑ s ∈ A ∩ B j, (L - value B a s)) = 0) ↔
      ∀ s ∈ A, value B a s = L := by
  classical
  constructor
  · rintro ⟨hA,hB⟩
    let r := fun s => L - value B a s
    have hr : ∑ s ∈ A, r s = 0 := hA
    have hb (j : β) : (∑ s ∈ A, if s ∈ B j then r s else 0) = 0 := by
      simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, r] using hB j
    have cross : ∑ s ∈ A, value B a s * r s = 0 := by
      simp only [value, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      calc
        _ = ∑ s ∈ A, a j * (if s ∈ B j then r s else 0) := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s ∈ B j <;> simp [h]
        _ = 0 := by rw [← Finset.mul_sum, hb, mul_zero]
    have sq : ∑ s ∈ A, (r s)^2 = 0 := by
      calc
        _ = ∑ s ∈ A, (L * r s - value B a s * r s) := by
          apply Finset.sum_congr rfl
          intro s _
          dsimp [r]
          ring
        _ = 0 := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hr, cross]; simp
    intro s hs
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (r x))).mp sq s hs
    have hzero : r s = 0 := by simpa using hz
    exact (sub_eq_zero.mp hzero).symm
  · intro h
    exact ⟨sum_eq_zero (fun s hs => by rw [h s hs, sub_self]),
      fun j => sum_eq_zero (fun s hs => by rw [h s (mem_inter.mp hs).1, sub_self])⟩

open scoped Classical in
/-- Every feature is contained in the union of clause falsifiers. Given the linear
    tests on each clause, total volumes compute exactly the size of that union. -/
theorem discovered_union_count {α β ι : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (A : ι → Finset α) (B : β → Finset α) (a : β → ℤ) (L : ℤ)
    (cover : ∀ j s, s ∈ B j → ∃ i, s ∈ A i)
    (tests : ∀ i, (∑ s ∈ A i, (L - value B a s)) = 0 ∧
      ∀ j, (∑ s ∈ A i ∩ B j, (L - value B a s)) = 0) :
    ∑ j, (B j).card * a j = (Fintype.card α : ℤ) * L -
      ((univ.filter (fun s => ∀ i, s ∉ A i)).card : ℤ) * L := by
  classical
  have expand : (∑ s, value B a s) = ∑ j, (B j).card * a j := by
    simp only [value]
    rw [Finset.sum_comm]
    simp
  rw [← expand, eq_sub_iff_add_eq]
  have complement : ((univ.filter (fun s => ∀ i, s ∉ A i)).card : ℤ) * L =
      ∑ s, if ∀ i, s ∉ A i then L else 0 := by simp [← Finset.sum_filter]
  rw [complement, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : α, L := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : ∀ i, s ∉ A i
      · have hnone (j : β) : s ∉ B j := by
          intro hj
          obtain ⟨i,hi⟩ := cover j s hj
          exact h i hi
        simp [value, h, hnone]
      · obtain ⟨i,hi⟩ := not_forall.mp h
        have hv := (local_equations_iff (A i) B a L).mp (tests i) s (by simpa using hi)
        simp [h, hv]
    _ = _ := by simp

open MvPolynomial

noncomputable def componentPoly {ι : Type*} :
    List (ι × Option ι) → MvPolynomial ι ℤ
  | [] => 0
  | (i,none)::t => X i + componentPoly t
  | (i,some p)::t => X i * (1-X p) + componentPoly t

def componentNumber (bad : ι → Bool) : List (ι × Option ι) → ℕ
  | [] => 0
  | (i,none)::t => (bad i).toNat + componentNumber bad t
  | (i,some p)::t => (bad i && !(bad p)).toNat + componentNumber bad t

theorem component_degree (e : List (ι × Option ι)) : (componentPoly e).totalDegree ≤ 2 := by
  induction e with
  | nil => simp [componentPoly]
  | cons v e ih =>
    obtain ⟨i, _ | p⟩ := v
    · exact (totalDegree_add ..).trans (max_le (by simp) ih)
    · apply (totalDegree_add ..).trans (max_le _ ih)
      apply (totalDegree_mul ..).trans
      have h := totalDegree_sub (1 : MvPolynomial ι ℤ) (X p)
      simp at h
      rw [totalDegree_X]
      omega

theorem component_eval (bad : ι → Bool) (e : List (ι × Option ι)) :
    eval (fun i => ((bad i).toNat : ℤ)) (componentPoly e) = componentNumber bad e := by
  induction e with
  | nil => simp [componentPoly, componentNumber]
  | cons v e ih =>
    obtain ⟨i, _ | p⟩ := v
    · simp [componentPoly, componentNumber, ih]
    · simp only [componentPoly, componentNumber, map_add, map_mul, map_sub, map_one,
        eval_X, ih, Nat.cast_add]
      cases bad i <;> cases bad p <;> simp

noncomputable def factors (p : MvPolynomial ι ℤ) : List ℤ → MvPolynomial ι ℤ
  | [] => 1
  | l::t => (C l - p) * factors p t

private theorem factors_degree (p : MvPolynomial ι ℤ) (z : List ℤ) :
    (factors p z).totalDegree ≤ p.totalDegree * z.length := by
  induction z with
  | nil => simp [factors]
  | cons l t ih =>
    have hh := totalDegree_sub (C l) p
    simp only [totalDegree_C, Nat.zero_max] at hh
    exact (totalDegree_mul ..).trans <| (Nat.add_le_add hh ih).trans_eq
      (by simp [Nat.mul_add, Nat.add_comm])

private theorem eval_factors (v : ι → ℤ) (p : MvPolynomial ι ℤ) (z : List ℤ) :
    eval v (factors p z) = (z.map fun l => l-eval v p).prod := by
  induction z with
  | nil => simp [factors]
  | cons l t ih => simp [factors, ih]

/-- A hidden tree with d distinct positive component counts supplies a degree-2d
    polynomial for the union. Its constant term vanishes by evaluation on all-zero flags. -/
theorem hidden_tree_lift (e : List (ι × Option ι)) (levels : List ℤ) :
    ∃ P : MvPolynomial ι ℤ, P.totalDegree ≤ 2*levels.length ∧
    eval (fun _ => 0) P = 0 ∧ ∀ bad : ι → Bool,
      ((componentNumber bad e : ℤ) = 0 ∨ (componentNumber bad e : ℤ) ∈ levels) →
      eval (fun i => ((bad i).toNat : ℤ)) P =
        if componentNumber bad e = 0 then 0 else levels.prod := by
  let H := componentPoly e
  refine ⟨C levels.prod - factors H levels, ?_, ?_, ?_⟩
  · apply (totalDegree_sub ..).trans
    rw [totalDegree_C, Nat.zero_max]
    exact (factors_degree H levels).trans (Nat.mul_le_mul_right _ (component_degree e))
  · have hz : eval (fun _ => (0 : ℤ)) H = 0 := by
      induction e with
      | nil => simp [H, componentPoly]
      | cons v t ih =>
        obtain ⟨i,_ | p⟩ := v <;> simpa [H, componentPoly] using ih
    rw [map_sub, eval_C, eval_factors, hz]
    simp
  · intro bad h
    simp only [map_sub, eval_C, eval_factors, H, component_eval]
    by_cases h0 : componentNumber bad e = 0
    · simp [h0]
    · have mem := h.resolve_left (by exact_mod_cast h0)
      have zero : (0 : ℤ) ∈ levels.map (fun l => l-(componentNumber bad e : ℤ)) :=
        List.mem_map.mpr ⟨_,mem,sub_self _⟩
      simp [h0, List.prod_eq_zero zero]

private theorem on_flags (P : MvPolynomial ι ℤ) (bad : ι → Bool) :
    eval (fun i => ((bad i).toNat : ℤ)) P =
      ∑ t ∈ P.support, if ∀ i ∈ t.support, bad i = true then P.coeff t else 0 := by
  classical
  rw [eval_eq]
  apply sum_congr rfl
  intro t _
  by_cases h : ∀ i ∈ t.support, bad i = true
  · have ho : ∏ i ∈ t.support, ((bad i).toNat : ℤ) ^ t i = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [h i hi])
    rw [ite_eq_left h, ho, mul_one]
  · obtain ⟨i, hi, hb⟩ : ∃ i ∈ t.support, bad i ≠ true := by push Not at h; exact h
    have hf : bad i = false := by simpa using hb
    have hz : ((bad i).toNat : ℤ)^t i = 0 := by
      simp [hf, zero_pow (Finsupp.mem_support_iff.mp hi)]
    have hp : ∏ i ∈ t.support, ((bad i).toNat : ℤ) ^ t i = 0 := Finset.prod_eq_zero hi hz
    rw [ite_eq_right h, hp, mul_zero]

open scoped Classical in
/-- Explicit coefficient dictionary for the hidden tree. Each feature is a nonempty
    intersection of at most twice as many clause events as there are levels. -/
theorem hidden_tree_intersections (e : List (ι × Option ι)) (levels : List ℤ) :
    ∃ (terms : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → ℤ),
      (∀ t ∈ terms, t.support.Nonempty ∧ t.support.card ≤ 2*levels.length) ∧
      ∀ bad : ι → Bool,
        ((componentNumber bad e : ℤ) = 0 ∨ (componentNumber bad e : ℤ) ∈ levels) →
        (∑ t ∈ terms, if ∀ i ∈ t.support, bad i = true then a t else 0) =
          if componentNumber bad e = 0 then 0 else levels.prod := by
  classical
  obtain ⟨P,deg,hzero,heval⟩ := hidden_tree_lift e levels
  refine ⟨P.support, P.coeff, ?_,fun bad hb => (on_flags P bad).symm.trans (heval bad hb)⟩
  intro t ht
  constructor
  · by_contra! hn
    have ht0 : t = 0 := Finsupp.support_eq_empty.mp hn
    subst t
    apply (MvPolynomial.mem_support_iff.mp ht)
    simpa [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] using hzero
  · have hle : ∑ _ ∈ t.support, 1 ≤ ∑ i ∈ t.support, t i :=
      sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    exact (by simpa [Finsupp.sum] using hle : t.support.card ≤ t.sum fun _ k => k).trans
      ((le_totalDegree ht).trans deg)

/-- Independent unit clauses realize the full Boolean trace. The coefficient of every
    nonempty intersection in a pointwise union formula on that trace is forced. -/
theorem full_trace_coefficients (a : Finset (Fin m) → ℤ) (L : ℤ)
    (h : ∀ S : Finset (Fin m), ∑ T ∈ S.powerset, a T = if S = ∅ then 0 else L)
    (S : Finset (Fin m)) :
    a S = (if S = ∅ then L else 0) - L * (-1)^S.card := by
  let b := fun T : Finset (Fin m) => (if T = ∅ then L else 0) - L * (-1)^T.card
  have hb (T : Finset (Fin m)) : ∑ U ∈ T.powerset, b U = if T = ∅ then 0 else L := by
    simp only [b, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_powerset_neg_one_pow_card]
    by_cases ht : T = ∅ <;> simp [ht]
  change a S = b S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have eqs := (h S).trans (hb S).symm
    have hm : S ∈ S.powerset := mem_powerset.mpr (by rfl)
    have he : ∑ T ∈ S.powerset.erase S, a T = ∑ T ∈ S.powerset.erase S, b T := by
      apply sum_congr rfl
      intro T hT
      obtain ⟨hne, hsub⟩ := mem_erase.mp hT
      exact ih T (ssubset_of_subset_of_ne (mem_powerset.mp hsub) hne)
    rw [← sum_erase_add _ a hm, ← sum_erase_add _ b hm, he] at eqs
    exact add_left_cancel eqs

/-- Two consecutive vertices can start at most one run, even with an incoming
    active predecessor. This supplies the sharp path example at every even size. -/
def runs (prev : Bool) : List Bool → ℕ
  | [] => 0
  | a::t => (a && !prev).toNat + runs a t

theorem path_bound (xs : List Bool) (prev : Bool) : 2*runs prev xs ≤ xs.length+1 := by
  match xs with
  | [] => simp [runs]
  | [a] => cases a <;> cases prev <;> decide
  | a::b::t =>
    have ih := path_bound t b
    cases a <;> cases b <;> cases prev <;> simp [runs] at * <;> omega

theorem units_realize (S : Finset (Fin m)) :
    ∃ s : Assignment, ∀ i : Fin m, Clause.eval s [(i.val,true)] = false ↔ i ∈ S := by
  let s : Assignment := fun j => if h : j < m then decide ((⟨j,h⟩ : Fin m) ∉ S) else false
  exact ⟨s,fun i => by simp [Clause.eval, Literal.eval, s, i.isLt]⟩

open scoped Classical in
/-- The implicit discovery equations instantiated with the repository's CNF semantics. -/
theorem discovered_model_count {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (row : α → Assignment) (cl : Fin m → Clause) (B : β → Finset α) (a : β → ℤ) (L : ℤ)
    (cover : ∀ j s, s ∈ B j → ∃ i, (cl i).eval (row s) = false)
    (tests : ∀ i, let A := univ.filter (fun s => (cl i).eval (row s) = false)
      (∑ s ∈ A, (L - value B a s)) = 0 ∧
      ∀ j, (∑ s ∈ A ∩ B j, (L - value B a s)) = 0) :
    ∑ j, (B j).card * a j = (Fintype.card α : ℤ) * L -
      ((univ.filter (fun s => CNF.eval (row s) (List.ofFn cl) = true)).card : ℤ) * L := by
  let A := fun i => univ.filter (fun s => (cl i).eval (row s) = false)
  have hc : ∀ j s, s ∈ B j → ∃ i, s ∈ A i := by simpa [A] using cover
  simpa [A, CNF.eval] using discovered_union_count A B a L hc tests

end ClauseSpan
