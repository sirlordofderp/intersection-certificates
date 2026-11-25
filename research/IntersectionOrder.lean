import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Sum

/-! Exact intersection orders for computing and recognizing short union identities.
    A population counts the points with each membership pattern. -/
namespace IntersectionOrder

open Finset MvPolynomial
open scoped BigOperators

abbrev Row (m : ℕ) := Finset (Fin m)
abbrev Population (m : ℕ) := Row m → ℕ
abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℤ

def flag (s : Row m) (i : Fin m) : ℤ := if i ∈ s then 1 else 0
noncomputable def atRow (P : Poly m) (s : Row m) := eval (flag s) P
def mass (μ : Population m) (f : Row m → ℤ) := ∑ s, (μ s : ℤ) * f s
def moment (μ : Population m) (T : Row m) := mass μ (fun s => if T ⊆ s then 1 else 0)
def Agree (k : ℕ) (μ ν : Population m) := ∀ T : Row m, T.card ≤ k → moment μ T = moment ν T

/-- Integer scaling allows rational union identities. P is a scaled indicator of
    the zero pattern. Its value at the origin is required even for absent origins. -/
def Fits (μ : Population m) (P : Poly m) : Prop :=
  atRow P ∅ ≠ 0 ∧ ∀ s, μ s ≠ 0 → s.Nonempty → atRow P s = 0

def HasDegree (d : ℕ) (μ : Population m) := ∃ P : Poly m, P.totalDegree ≤ d ∧ Fits μ P

private theorem mono_flags (t : Fin m →₀ ℕ) (s : Row m) :
    (∏ i ∈ t.support, (flag s i)^(t i)) = if t.support ⊆ s then 1 else 0 := by
  classical
  by_cases h : t.support ⊆ s
  · rw [ite_eq_left h]
    exact prod_eq_one fun i hi => by simp [flag, h hi]
  · obtain ⟨i,hi,hs⟩ := Finset.not_subset.mp h
    rw [ite_eq_right h]
    apply prod_eq_zero hi
    simp [flag, hs, Finsupp.mem_support_iff.mp hi]

private theorem mass_expansion (μ : Population m) (P : Poly m) :
    mass μ (atRow P) = ∑ t ∈ P.support, P.coeff t * moment μ t.support := by
  classical
  simp only [mass, atRow, eval_eq, mono_flags, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro t _
  simp only [moment, mass, Finset.mul_sum]
  apply sum_congr rfl
  intro s _
  ring

theorem polynomial_transfer {μ ν : Population m} (h : Agree k μ ν) (P : Poly m) (hd : P.totalDegree ≤ k) :
    mass μ (atRow P) = mass ν (atRow P) := by
  classical
  rw [mass_expansion, mass_expansion]
  apply sum_congr rfl
  intro t ht
  have hle : ∑ _ ∈ t.support, 1 ≤ ∑ i ∈ t.support, t i :=
    sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hcard : t.support.card ≤ t.sum fun _ k => k := by simpa [Finsupp.sum] using hle
  rw [h _ (hcard.trans ((le_totalDegree ht).trans hd))]

private theorem cross_mass {μ : Population m} {P : Poly m} (h : Fits μ P) (Q : Poly m) :
    mass μ (atRow (P*Q)) = μ ∅ * (atRow P ∅ * atRow Q ∅) := by
  unfold mass
  rw [sum_eq_single (∅ : Row m)]
  · simp [atRow]
  · intro s _ hs
    by_cases hm : μ s = 0
    · simp [hm]
    · have hz := h.2 s hm (Finset.nonempty_iff_ne_empty.mpr hs)
      change (μ s : ℤ) * eval (flag s) (P*Q) = 0
      rw [map_mul, show eval (flag s) P = 0 from hz, zero_mul, mul_zero]
  · simp

/-- If both systems admit the promised degree, moments through 2d determine the
    number of uncovered points even when the two certificates differ. -/
theorem count_transfer (h : Agree (2*d) μ ν) (a : HasDegree d μ) (b : HasDegree d ν) :
    μ ∅ = ν ∅ := by
  obtain ⟨P,hp,ha⟩ := a
  obtain ⟨Q,hq,hb⟩ := b
  have deg := (totalDegree_mul P Q).trans (Nat.add_le_add hp hq)
  have eq := polynomial_transfer h (P*Q) (by simpa [two_mul] using deg)
  rw [cross_mass ha, mul_comm P Q, cross_mass hb, mul_comm (atRow Q ∅) (atRow P ∅)] at eq
  exact_mod_cast mul_right_cancel₀ (mul_ne_zero ha.1 hb.1) eq

noncomputable def weight (m : ℕ) : Poly m := ∑ i : Fin m, X i

theorem weight_eval (s : Row m) : atRow (weight m) s = s.card := by
  simp [weight, atRow, flag]

private theorem weight_degree (m : ℕ) : (weight m).totalDegree ≤ 1 := by
  unfold weight
  induction (univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [sum_insert hi]
    exact (totalDegree_add ..).trans (max_le (by simp) ih)

private theorem residual (μ : Population m) (P : Poly m) :
    mass μ (atRow (weight m * (P*P))) = 0 ↔
      ∀ s, μ s ≠ 0 → s.Nonempty → atRow P s = 0 := by
  have point (s : Row m) : atRow (weight m * (P*P)) s =
      (s.card : ℤ) * (atRow P s)^2 := by
    rw [← weight_eval s]
    simp [atRow, pow_two]
  simp only [mass, point]
  constructor
  · intro hz s hm hs
    have nn (x : Row m) : 0 ≤ (μ x : ℤ) * (x.card * (atRow P x)^2) :=
      mul_nonneg (Int.natCast_nonneg _) (mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _))
    have v := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nn x)).mp hz s (mem_univ _)
    have hm' : (μ s : ℤ) ≠ 0 := by exact_mod_cast hm
    have hc : (s.card : ℤ) ≠ 0 := by exact_mod_cast (card_pos.mpr hs).ne'
    have hsq := (mul_eq_zero.mp ((mul_eq_zero.mp v).resolve_left hm')).resolve_left hc
    simpa using hsq
  · intro h
    apply sum_eq_zero
    intro s _
    by_cases hm : μ s = 0
    · simp [hm]
    by_cases hs : s = ∅
    · simp [hs]
    simp [h s hm (nonempty_iff_ne_empty.mpr hs)]

/-- One additional order transfers the certificate itself. -/
theorem certificate_transfer {μ ν : Population m} (h : Agree (2*d+1) μ ν) (P : Poly m)
    (hd : P.totalDegree ≤ d) : Fits μ P ↔ Fits ν P := by
  have deg := (totalDegree_mul (weight m) (P*P)).trans
    (Nat.add_le_add (weight_degree m) ((totalDegree_mul P P).trans (Nat.add_le_add hd hd)))
  have eq := polynomial_transfer h (weight m * (P*P)) (by omega)
  simp only [Fits, ← residual, eq]

def half (p : ℕ) : Population m := fun s => if s.card % 2 = p then 1 else 0

private theorem moment_half (T : Row m) (p : ℕ) :
    moment (half p) T = ∑ s ∈ (univ : Row m).powerset,
      (if T ⊆ s ∧ s.card % 2 = p then (1 : ℤ) else 0) := by
  simp only [moment,mass,half,powerset_univ]
  apply sum_congr rfl
  intro s _
  by_cases h : T ⊆ s <;> by_cases hp : s.card % 2 = p <;> simp [h,hp]

/-- Every labelled proper intersection has equal size on the two parity halves. -/
theorem proper_moments (h : k < m) : Agree k (@half m 0) (half 1) := by
  intro T ht
  obtain ⟨i,hi⟩ : ∃ i : Fin m, i ∉ T := by
    by_contra! hall
    have he : T = univ := eq_univ_of_forall hall
    simp [he] at ht
    omega
  let W : Row m := univ.erase i
  have hw : i ∉ W := Finset.notMem_erase i univ
  have he : (univ : Row m) = insert i W := (insert_erase (mem_univ i)).symm
  rw [moment_half, moment_half, he, sum_powerset_insert hw, sum_powerset_insert hw,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  have hn : i ∉ s := fun his => hw ((mem_powerset.mp hs) his)
  have hsub : T ⊆ insert i s ↔ T ⊆ s := by
    constructor
    · intro hh j hj
      rcases mem_insert.mp (hh hj) with eq | hm
      · exact (hi (eq ▸ hj)).elim
      · exact hm
    · exact fun hh => hh.trans (subset_insert ..)
  rw [card_insert_of_notMem hn]
  by_cases sub : T ⊆ s <;> simp only [hsub, sub, true_and, false_and, ite_false]
  split_ifs <;> omega

noncomputable def avoid (m start : ℕ) : ℕ → Poly m
  | 0 => 1
  | d+1 => (C ((start+2*d : ℕ) : ℤ) - weight m) * avoid m start d

private theorem avoid_degree (m start d : ℕ) : (avoid m start d).totalDegree ≤ d := by
  induction d with
  | zero => simp [avoid]
  | succ d ih =>
    have hh := totalDegree_sub (C ((start+2*d : ℕ) : ℤ)) (weight m)
    simp only [totalDegree_C, Nat.zero_max] at hh
    exact (totalDegree_mul ..).trans (by have := Nat.add_le_add (hh.trans (weight_degree m)) ih; omega)

private theorem avoid_origin (m start d : ℕ) (hs : 0 < start) : atRow (avoid m start d) ∅ ≠ 0 := by
  induction d with
  | zero => simp [avoid, atRow]
  | succ d ih =>
    have hw := weight_eval (∅ : Row m)
    change eval (flag ∅) (weight m) = _ at hw
    simp only [card_empty, Nat.cast_zero] at hw
    simp only [avoid, atRow, map_mul, map_sub, eval_C, hw, sub_zero]
    exact mul_ne_zero (by exact_mod_cast (show start+2*d ≠ 0 by omega)) ih

private theorem avoid_hit (s : Row m) (start d j : ℕ) (hj : j < d)
    (hw : s.card = start + 2*j) : atRow (avoid m start d) s = 0 := by
  induction d with
  | zero => omega
  | succ d ih =>
    simp only [avoid, atRow, map_mul, map_sub, eval_C]
    by_cases he : j = d
    · subst j
      rw [show eval (flag s) (weight m) = s.card from weight_eval s, hw, sub_self, zero_mul]
    · exact mul_eq_zero_of_right _ (ih (by omega))

private theorem half_fits (d m p : ℕ) (hp : p < 2) (hm : m ≤ 2*d + (1-p)) :
    HasDegree d (@half m p) := by
  let start := 2-p
  refine ⟨avoid m start d, avoid_degree .., avoid_origin _ _ _ (by dsimp [start]; omega), ?_⟩
  intro s hs hn
  have parity : s.card % 2 = p := by simpa [half] using hs
  have pos := card_pos.mpr hn
  have cap : s.card ≤ m := by simpa using (card_le_univ s)
  exact avoid_hit s start d ((s.card-start)/2) (by dsimp [start]; omega) (by dsimp [start]; omega)

private theorem odd_impossible (d : ℕ) : ¬ HasDegree d (@half (2*d+1) 1) := by
  rintro ⟨P,hd,hfit⟩
  let m := 2*d+1
  have odd_zero : mass (@half m 1) (atRow (P*P)) = 0 := by
    rw [cross_mass hfit]
    simp [half]
  have deg := (totalDegree_mul P P).trans (Nat.add_le_add hd hd)
  have eq := polynomial_transfer (proper_moments (show 2*d < m by dsimp [m]; omega))
    (P*P) (by simpa [two_mul] using deg)
  have even_zero := eq.trans odd_zero
  have nn (s : Row m) : 0 ≤ ((half 0 s : ℕ) : ℤ) * atRow (P*P) s := by
    apply mul_nonneg (Int.natCast_nonneg _)
    simp only [atRow, map_mul]
    exact mul_self_nonneg _
  have ee := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => nn s)).mp even_zero ∅ (mem_univ _)
  have hz : atRow P ∅ * atRow P ∅ = 0 := by simpa [half,atRow] using ee
  exact mul_ne_zero hfit.1 hfit.1 hz

/-- Both sides satisfy the promise and all intersections below order 2d agree.
    The numbers of uncovered points differ. -/
theorem counting_sharp (d : ℕ) (hd : 0 < d) :
    ∃ μ ν : Population (2*d), Agree (2*d-1) μ ν ∧
      HasDegree d μ ∧ HasDegree d ν ∧ μ ∅ ≠ ν ∅ := by
  refine ⟨half 0,half 1,proper_moments (by omega),half_fits _ _ _ (by decide) (by omega),
    half_fits _ _ _ (by decide) (by omega), ?_⟩
  simp [half]

/-- At order 2d the same data admit a degree-d system and forbid one on its partner. -/
theorem recognition_sharp (d : ℕ) :
    ∃ μ ν : Population (2*d+1), Agree (2*d) μ ν ∧ HasDegree d μ ∧ ¬ HasDegree d ν :=
  ⟨half 0,half 1,proper_moments (by omega),half_fits _ _ _ (by decide) (by omega),
    odd_impossible d⟩

/-- A normalized projection residual r has r(∅)=L and is orthogonal to L-r.
    The unweighted squared error on the covered points then has a computable form. -/
theorem projection_gap (μ : Population m) (r : Row m → ℤ) (L : ℤ)
    (hr : r ∅ = L) (orth : mass μ (fun s => r s * (L-r s)) = 0) :
    L * mass μ r - μ ∅ * L^2 =
      ∑ s ∈ (univ : Finset (Row m)).erase ∅, (μ s : ℤ) * r s ^ 2 := by
  have norm : L * mass μ r = ∑ s, (μ s : ℤ) * r s^2 := by
    apply sub_eq_zero.mp
    rw [← orth]
    simp only [mass, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro s _
    ring
  rw [norm, ← Finset.sum_erase_add _ _ (mem_univ (∅ : Row m)), hr]
  ring

/-- The next available moment order also bounds the uncovered count when the
    degree promise fails. Integer rounding can close the bounds to a singleton. -/
theorem weighted_gap_bounds (μ : Population m) (r : Row m → ℤ) (L : ℤ)
    (hr : r ∅ = L) (orth : mass μ (fun s => r s * (L-r s)) = 0) :
    let gap := L * mass μ r - μ ∅ * L^2
    let err := mass μ (fun s => (s.card : ℤ) * r s^2)
    gap ≤ err ∧ err ≤ (m : ℤ) * gap := by
  dsimp only
  rw [projection_gap μ r L hr orth]
  unfold mass
  rw [← sum_erase_add _ (fun s : Row m => (μ s : ℤ) * (s.card * r s^2)) (mem_univ ∅)]
  simp only [card_empty, Nat.cast_zero, zero_mul, mul_zero, add_zero, Finset.mul_sum]
  constructor
  · apply sum_le_sum
    intro s hs
    have hpos := card_pos.mpr (nonempty_iff_ne_empty.mpr (mem_erase.mp hs).1)
    have hc : (1 : ℤ) ≤ s.card := by exact_mod_cast hpos
    apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
    simpa using mul_le_mul_of_nonneg_right hc (sq_nonneg (r s))
  · apply sum_le_sum
    intro s _
    have hc : (s.card : ℤ) ≤ m := by exact_mod_cast (show s.card ≤ m by simpa using card_le_univ s)
    calc
      _ ≤ (μ s : ℤ) * (m * r s^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (Int.natCast_nonneg _)
      _ = _ := by ring

/-- Each macro bit is represented by a length-t parity block. All ones encode true.
    A block query asks that each position of Q be one. -/
def blockMoment (μ : Population m) (Q : Fin m → Row t) : ℤ :=
  ∑ A, (μ A : ℤ) * ∏ i, moment (@half t (if i ∈ A then t%2 else 1-t%2)) (Q i)

def decode (x : Fin m → Row t) : Row m :=
  univ.filter fun i => (x i).card%2 = t%2

/-- The product formula counts actual encoded Boolean rows with their multiplicities. -/
theorem block_counts_rows (μ : Population m) (Q : Fin m → Row t) :
    blockMoment μ Q = ∑ x : Fin m → Row t, (μ (decode x) : ℤ) *
      (if ∀ i, Q i ⊆ x i then 1 else 0) := by
  classical
  let term := fun (A : Row m) (i : Fin m) (v : Row t) =>
    ((half (if i ∈ A then t%2 else 1-t%2) v : ℕ) : ℤ) * (if Q i ⊆ v then 1 else 0)
  change (∑ A, (μ A : ℤ) * ∏ i, ∑ v, term A i v) = _
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  have good (i : Fin m) : (x i).card%2 = (if i ∈ decode x then t%2 else 1-t%2) := by
    simp only [decode,mem_filter,mem_univ,true_and]
    split <;> omega
  have bad (A : Row m) (ha : A ≠ decode x) :
      ∏ i, term A i (x i) = 0 := by
    have diff : ∃ i, ¬ (i ∈ A ↔ i ∈ decode x) := by
      by_contra! same
      exact ha (Finset.ext same)
    obtain ⟨i,hi⟩ := diff
    apply prod_eq_zero (mem_univ i)
    simp only [decode,mem_filter,mem_univ,true_and] at hi
    by_cases a : i ∈ A
    · have hn : (x i).card%2 ≠ t%2 := fun eq => hi (iff_of_true a eq)
      simp [term, half, a, hn]
    · have eq : (x i).card%2 = t%2 := by
        by_contra hn
        exact hi (iff_of_false a hn)
      have hn : (x i).card%2 ≠ 1-t%2 := by omega
      simp [term, half, a, hn]
  rw [Finset.sum_eq_single (decode x)]
  · by_cases fits : ∀ i, Q i ⊆ x i
    · have ho : ∏ i, term (decode x) i (x i) = 1 :=
        prod_eq_one fun i _ => by simp [term,half,good i,fits i]
      rw [ho,ite_eq_left fits]
    · obtain ⟨i,hi⟩ := not_forall.mp fits
      have hz : ∏ j, term (decode x) j (x j) = 0 :=
        prod_eq_zero (mem_univ i) (by simp [term,hi])
      rw [hz,ite_eq_right fits]
  · intro A _ ha
    rw [bad A ha,mul_zero]
  · simp

def filled (Q : Fin m → Row t) := univ.filter (fun i => Q i = univ)
def factor (Q : Fin m → Row t) : ℤ :=
  ∏ i, if Q i = univ then 1 else moment (half 0) (Q i)

private theorem full_half (t p : ℕ) : moment (@half t p) univ =
    if t%2 = p then 1 else 0 := by
  simp [moment, mass, half, Finset.univ_subset_iff]

private theorem block_response (A : Row m) (Q : Fin m → Row t) (i : Fin m) :
    moment (@half t (if i ∈ A then t%2 else 1-t%2)) (Q i) =
      (if Q i = univ then 1 else moment (half 0) (Q i)) *
      (if Q i = univ ∧ i ∉ A then 0 else 1) := by
  by_cases q : Q i = univ
  · have neq : t%2 ≠ 1-t%2 := by omega
    by_cases a : i ∈ A <;> simp [q,full_half,a,neq]
  · have lt : (Q i).card < t := by
      simpa using card_lt_card (ssubset_univ_iff.mpr q)
    have same := proper_moments lt (Q i) (le_refl _)
    have p : (if i ∈ A then t%2 else 1-t%2) = 0 ∨
        (if i ∈ A then t%2 else 1-t%2) = 1 := by split <;> omega
    rcases p with h | h <;> simp [q,h,same]

theorem block_factorization (μ : Population m) (Q : Fin m → Row t) :
    blockMoment μ Q = factor Q * moment μ (filled Q) := by
  classical
  unfold blockMoment
  conv_rhs => unfold moment mass
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro A _
  have each := block_response A Q
  simp_rw [each, Finset.prod_mul_distrib]
  change _ * (factor Q * _) = _
  by_cases h : filled Q ⊆ A
  · have hh (i : Fin m) : ¬ (Q i = univ ∧ i ∉ A) :=
      fun ⟨hi,ha⟩ => ha (h (mem_filter.mpr ⟨mem_univ _,hi⟩))
    simp [h, hh, mul_comm]
  · obtain ⟨i,hi,ha⟩ := Finset.not_subset.mp h
    have hq : Q i = univ := (mem_filter.mp hi).2
    have hz : (∏ j : Fin m, (if Q j = univ ∧ j ∉ A then (0:ℤ) else 1)) = 0 :=
      prod_eq_zero (i := i) (mem_univ _) (by simp [hq,ha])
    simp [h, hz]

def BlockAgree (k t : ℕ) (μ ν : Population m) := ∀ Q : Fin m → Row t,
    (∑ i, (Q i).card) ≤ k → blockMoment μ Q = blockMoment ν Q

private theorem half_empty_pos (t : ℕ) : 0 < moment (@half t 0) ∅ := by
  have hz := Finset.single_le_sum (f := fun s : Row t => ((half 0 s : ℕ) : ℤ))
    (fun s _ => Int.natCast_nonneg _) (mem_univ (∅ : Row t))
  simp [moment, mass, half] at hz ⊢
  exact hz

/-- Raw conjunction data at order k are equivalent to the original data at
    floor(k/t). The equivalence is for every pair of finite populations. -/
theorem block_order_iff (μ ν : Population m) (t k : ℕ) (ht : 0 < t) :
    BlockAgree k t μ ν ↔ Agree (k/t) μ ν := by
  classical
  have ne : (∅ : Row t) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  constructor
  · intro h S hs
    let Q : Fin m → Row t := fun i => if i ∈ S then univ else ∅
    have fill : filled Q = S := by ext i; by_cases hi : i ∈ S <;> simp [filled,Q,hi,ne]
    have cost : (∑ i, (Q i).card) = S.card*t := by
      simp [Q, apply_ite Finset.card]
    have pos : 0 < factor Q := by
      apply Finset.prod_pos
      intro i _
      by_cases h : i ∈ S
      · simp [Q,h]
      · simpa [Q,h,ne] using half_empty_pos t
    have eq := h Q (cost.trans_le ((Nat.le_div_iff_mul_le ht).mp hs))
    rw [block_factorization, block_factorization, fill] at eq
    exact mul_left_cancel₀ pos.ne' eq
  · intro h Q cost
    have size : (filled Q).card*t ≤ ∑ i, (Q i).card := by
      calc
        _ = ∑ i : Fin m, if i ∈ filled Q then t else 0 := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro i _
          by_cases hi : i ∈ filled Q
          · simp [hi, (mem_filter.mp hi).2]
          · simp [hi]
    rw [block_factorization, block_factorization, h _ ((Nat.le_div_iff_mul_le ht).mpr (size.trans cost))]

/-- More generally, any nonnegative polynomial detector H separates the region
    to be covered (H positive) from its complement (H zero). -/
theorem detector_transfer {μ ν : Population m} (H P : Poly m)
    (hh : H.totalDegree ≤ t) (hp : P.totalDegree ≤ d) (pos : ∀ s, 0 ≤ atRow H s)
    (agree : Agree (2*d+t) μ ν) :
    (∀ s, μ s ≠ 0 → atRow H s ≠ 0 → atRow P s = 0) ↔
    (∀ s, ν s ≠ 0 → atRow H s ≠ 0 → atRow P s = 0) := by
  have criterion (a : Population m) :
      (∀ s, a s ≠ 0 → atRow H s ≠ 0 → atRow P s = 0) ↔ mass a (atRow (H*(P*P))) = 0 := by
    have pt (s : Row m) : atRow (H*(P*P)) s = atRow H s * (atRow P s)^2 := by
      simp [atRow, pow_two]
    simp only [mass, pt]
    constructor
    · intro hv
      apply sum_eq_zero
      intro s _
      by_cases hz : a s = 0
      · simp [hz]
      by_cases h : atRow H s = 0
      · simp [h]
      simp [hv s hz h]
    · intro hz s ha hH
      have nn (u : Row m) : 0 ≤ (a u : ℤ) * (atRow H u * (atRow P u)^2) :=
        mul_nonneg (Int.natCast_nonneg _) (mul_nonneg (pos _) (sq_nonneg _))
      have eq := (sum_eq_zero_iff_of_nonneg (fun u _ => nn u)).mp hz s (mem_univ _)
      have ha' : (a s : ℤ) ≠ 0 := by exact_mod_cast ha
      have sq := (mul_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left ha')).resolve_left hH
      simpa using sq
  rw [criterion, criterion]
  have deg := (totalDegree_mul H (P*P)).trans
    (Nat.add_le_add hh ((totalDegree_mul P P).trans (Nat.add_le_add hp hp)))
  rw [polynomial_transfer agree _ (by omega : (H*(P*P)).totalDegree ≤ 2*d+t)]

private theorem div_before (a t : ℕ) (ha : 0 < a) (ht : 0 < t) : (a*t-1)/t = a-1 := by
  apply Nat.le_antisymm
  · have h : (a*t-1)/t < a := (Nat.div_lt_iff_lt_mul ht).mpr (by have := Nat.mul_pos ha ht; omega)
    omega
  · apply (Nat.le_div_iff_mul_le ht).mpr
    have eq : (a-1)*t+t = a*t := by rw [← Nat.succ_mul]; congr 1; omega
    omega

theorem block_counting_sharp (d t : ℕ) (hd : 0 < d) (ht : 0 < t) :
    ∃ μ ν : Population (2*d), BlockAgree (2*d*t-1) t μ ν ∧
      HasDegree d μ ∧ HasDegree d ν ∧ μ ∅ ≠ ν ∅ := by
  obtain ⟨μ,ν,agree,ha,hb,ne⟩ := counting_sharp d hd
  exact ⟨μ,ν,(block_order_iff μ ν t _ ht).mpr (by rwa [div_before _ _ (by omega) ht]),
    ha,hb,ne⟩

theorem block_recognition_sharp (d t : ℕ) (ht : 0 < t) :
    ∃ μ ν : Population (2*d+1), BlockAgree ((2*d+1)*t-1) t μ ν ∧ HasDegree d μ ∧ ¬ HasDegree d ν := by
  obtain ⟨μ,ν,agree,ha,hb⟩ := recognition_sharp d
  exact ⟨μ,ν,(block_order_iff μ ν t _ ht).mpr (by rw [div_before _ _ (by omega) ht]; exact agree),ha,hb⟩

/-- Aggregation discards the labels of the intersections of each fixed order. -/
def layer (μ : Population m) (j : ℕ) : ℤ :=
  ∑ T ∈ (univ : Row m).powersetCard j, moment μ T

theorem layer_by_weight (μ : Population m) (j : ℕ) :
    layer μ j = mass μ (fun s => s.card.choose j) := by
  classical
  unfold layer moment mass
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [← mul_sum, ← sum_filter]
  have he : ((univ : Row m).powersetCard j).filter (fun T => T ⊆ s) = s.powersetCard j := by
    ext T
    simp [and_comm]
  simp [he,card_powersetCard]

private def initial (s : Row m) : Row m :=
  univ.map (Fin.castLEEmb (show s.card ≤ m by simpa using card_le_univ s))

private theorem initial_card (s : Row m) : (initial s).card = s.card := by simp [initial]

private theorem initial_mem (s : Row m) (i : Fin m) : i ∈ initial s ↔ i.val < s.card := by
  constructor
  · intro h
    obtain ⟨j,_,rfl⟩ := mem_map.mp h
    exact j.isLt
  · intro h
    exact mem_map.mpr ⟨⟨i.val,h⟩,mem_univ _,Fin.ext rfl⟩

private def chainPop (μ : Population m) : Population m :=
  fun s => ∑ x, if s = initial x then μ x else 0

private theorem chain_mass (μ : Population m) (f : Row m → ℤ) :
    mass (chainPop μ) f = mass μ (fun s => f (initial s)) := by
  classical
  simp only [mass,chainPop,Nat.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_eq_single (initial x)]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

private theorem chain_layer (μ : Population m) (j : ℕ) : layer (chainPop μ) j = layer μ j := by
  simp only [layer_by_weight, chain_mass, initial_card]

private theorem chain_origin (μ : Population m) : chainPop μ ∅ = μ ∅ := by
  unfold chainPop
  rw [sum_eq_single (∅ : Row m)]
  · have hi : initial (∅ : Row m) = ∅ := card_eq_zero.mp (by rw [initial_card]; rfl)
    simp [hi]
  · intro s _ hs
    have hn : ∅ ≠ initial s := by
      intro eq
      have hc := congrArg card eq
      simp only [card_empty,initial_card] at hc
      exact hs (card_eq_zero.mp hc.symm)
    simp [hn]
  · simp

def IsChain (μ : Population m) := ∀ s, μ s ≠ 0 → ∀ i j : Fin m, i ≤ j → j ∈ s → i ∈ s

private theorem nested (μ : Population m) : IsChain (chainPop μ) := by
  intro s h i j hij hj
  obtain ⟨x,_,hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases he : s = initial x
  · subst s
    exact (initial_mem x i).mpr (Nat.lt_of_le_of_lt hij ((initial_mem x j).mp hj))
  · simp [he] at hx

private theorem chain_fits {μ : Population m} (hm : 0 < m) (hc : IsChain μ) : HasDegree 1 μ := by
  let i : Fin m := ⟨0,hm⟩
  refine ⟨1-X i,(totalDegree_sub ..).trans (by simp),?_,?_⟩
  · simp [atRow,flag]
  · intro s hs hn
    obtain ⟨j,hj⟩ := hn
    have hi := hc s hs i j (Nat.zero_le _) hj
    simp [atRow,flag,hi]

theorem aggregate_count (μ : Population m) :
    ∑ j ∈ range (m+1), (-1:ℤ)^j * layer μ j = μ ∅ := by
  have row (s : Row m) : ∑ j ∈ range (m+1), ((-1:ℤ)^j * s.card.choose j) =
      if s = ∅ then 1 else 0 := by
    have hcap : s.card ≤ m := by simpa using card_le_univ s
    have eq : (∑ j ∈ range (s.card+1), ((-1:ℤ)^j * s.card.choose j)) =
        ∑ j ∈ range (m+1), ((-1:ℤ)^j * s.card.choose j) := by
      apply sum_subset (range_mono (Nat.succ_le_succ hcap))
      intro j _ hj
      have lt : s.card < j := by simp at hj; omega
      simp [Nat.choose_eq_zero_of_lt lt]
    rw [← eq, Int.alternating_sum_range_choose]
    simp
  simp only [layer_by_weight, mass, Finset.mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ s, (μ s : ℤ) * (if s = ∅ then 1 else 0) := by
      apply sum_congr rfl
      intro s _
      rw [← row s, mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by simp

/-- Even nested families of degree one require order m when only layer totals are
    available. Both have the first event as their union, with the same fixed order. -/
theorem aggregate_sharp (m : ℕ) (hm : 0 < m) :
    ∃ μ ν : Population m, IsChain μ ∧ IsChain ν ∧ HasDegree 1 μ ∧ HasDegree 1 ν ∧
      (∀ j < m, layer μ j = layer ν j) ∧ μ ∅ ≠ ν ∅ := by
  refine ⟨chainPop (half 0),chainPop (half 1),nested _,nested _,chain_fits hm (nested _),
    chain_fits hm (nested _),?_,?_⟩
  · intro j hj
    rw [chain_layer,chain_layer]
    apply sum_congr rfl
    intro T ht
    exact proper_moments hj T (mem_powersetCard.mp ht).2.le
  · simp [chain_origin,half]

end IntersectionOrder
