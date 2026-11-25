import PEqualNP.Defs.Search
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Int

namespace ClauseTrees

open Finset
open PEqualNP.Search

abbrev Row (n : ℕ) := Fin n → Bool

/-- An ordinary normalized nontautological clause, encoded by its falsification cube. -/
structure Cube (n : ℕ) where
  vars : Finset (Fin n)
  bits : Row n

noncomputable def Cube.clause (c : Cube n) : Clause :=
  c.vars.toList.map fun i => (i.val, !(c.bits i))

def extend (s : Row n) : Assignment := fun i => if h : i < n then s ⟨i,h⟩ else false

def Cube.rows (c : Cube n) : Finset (Row n) :=
  Fintype.piFinset fun i => if i ∈ c.vars then {c.bits i} else univ

@[simp] theorem mem_rows (c : Cube n) (s : Row n) :
    s ∈ c.rows ↔ ∀ i ∈ c.vars, s i = c.bits i := by
  simp only [Cube.rows, Fintype.mem_piFinset]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ c.vars
    · simpa [hi] using h i hi
    · simp only [hi, ite_false, mem_univ]

theorem clause_false (c : Cube n) (s : Row n) :
    c.clause.eval (extend s) = false ↔ s ∈ c.rows := by
  simp [Cube.clause, Clause.eval, Literal.eval, List.any_eq_false, extend]

theorem cube_mass (c : Cube n) : c.rows.card * 2 ^ c.vars.card = 2 ^ n := by
  have h : (∏ i : Fin n, if i ∈ c.vars then 2 else 1) = 2 ^ c.vars.card := by
    simp
  rw [← h, Cube.rows, Fintype.card_piFinset, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ _ : Fin n, 2 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ c.vars <;> simp [hi]
    _ = _ := by simp

/-- On at least half the child's rows, a non-subsuming parent is satisfied. -/
theorem edge_half (p c : Cube n)
    (h : ∃ i ∈ p.vars, i ∉ c.vars ∨ p.bits i ≠ c.bits i) :
    c.rows.card ≤ 2 * (c.rows \ p.rows).card := by
  obtain ⟨i, hp, hi⟩ := h
  by_cases hc : i ∈ c.vars
  · have hn := hi.resolve_left (by simpa using hc)
    have he : c.rows \ p.rows = c.rows := by
      ext s
      simp only [mem_sdiff, and_iff_left_iff_imp]
      intro hs hs'
      exact hn (((mem_rows _ _).1 hs' i hp).symm.trans ((mem_rows _ _).1 hs i hc))
    rw [he]
    omega
  · let d : Cube n := ⟨insert i c.vars, Function.update c.bits i (!(p.bits i))⟩
    have sub : d.rows ⊆ c.rows \ p.rows := by
      intro s hs
      have hd := (mem_rows _ _).1 hs
      apply mem_sdiff.mpr
      constructor
      · apply (mem_rows _ _).2
        intro j hj
        have hji : j ≠ i := by rintro rfl; contradiction
        simpa [d, Function.update_of_ne hji] using hd j (mem_insert_of_mem hj)
      · intro hs'
        have hh := (mem_rows _ _).1 hs' i hp
        have hu := hd i (mem_insert_self ..)
        simp [d, hh] at hu
    have equalMass := (cube_mass c).trans (cube_mass d).symm
    have dv : d.vars.card = c.vars.card + 1 := card_insert_of_notMem hc
    rw [dv, pow_succ] at equalMass
    have hh : c.rows.card = 2 * d.rows.card := by
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos c.vars.card)
        (by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using equalMass)
    have := card_le_card sub
    omega

/-- One root event and one child-false/parent-true event per oriented edge. -/
def events (r : Cube n) (edges : List (Cube n × Cube n)) : List (Finset (Row n)) :=
  r.rows :: edges.map fun e => e.2.rows \ e.1.rows

def starts {α : Type*} [DecidableEq α] (s : α) (E : List (Finset α)) : ℕ :=
  (E.map fun A => if s ∈ A then 1 else 0).sum

theorem double_count {α : Type*} [Fintype α] [DecidableEq α] (E : List (Finset α)) :
    (E.map Finset.card).sum = ∑ s : α, starts s E := by
  induction E with
  | nil => simp [starts]
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [starts, List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    simp

private theorem edge_mass (p c : Cube n) (w : ℕ) (hw : c.vars.card ≤ w)
    (ha : ∃ i ∈ p.vars, i ∉ c.vars ∨ p.bits i ≠ c.bits i) :
    2 ^ n ≤ (c.rows \ p.rows).card * 2 ^ (w+1) := by
  calc
    2 ^ n = c.rows.card * 2 ^ c.vars.card := (cube_mass c).symm
    _ ≤ (2 * (c.rows \ p.rows).card) * 2 ^ w :=
      Nat.mul_le_mul (edge_half p c ha) (Nat.pow_le_pow_right (by decide) hw)
    _ = _ := by rw [pow_succ]; ac_rfl

theorem width_mass (r : Cube n) (edges : List (Cube n × Cube n)) (w : ℕ)
    (hr : r.vars.card ≤ w)
    (he : ∀ e ∈ edges, e.2.vars.card ≤ w ∧
      ∃ i ∈ e.1.vars, i ∉ e.2.vars ∨ e.1.bits i ≠ e.2.bits i) :
    (edges.length + 2) * 2 ^ n ≤
      ((events r edges).map Finset.card).sum * 2 ^ (w+1) := by
  have hr' : 2 ^ n ≤ r.rows.card * 2 ^ w :=
    (cube_mass r).symm.le.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr))
  induction edges with
  | nil =>
    simp [events, pow_succ, Nat.mul_comm, Nat.mul_assoc] at *
    omega
  | cons e t ih =>
    have ⟨hw, ha⟩ := he e (.head ..)
    have hn := edge_mass e.1 e.2 w hw ha
    have ht := ih (fun f hf => he f (.tail _ hf))
    simp only [events, List.map_cons, List.sum_cons, List.length_cons] at *
    rw [show t.length + 1 + 2 = (t.length + 2) + 1 by omega, Nat.add_mul, one_mul]
    apply (Nat.add_le_add ht hn).trans_eq
    simp only [Nat.add_mul]
    omega

/-- The capacity bound for any rooted tree, or path, with at most k starts per row.
    Only the root and the oriented edges enter the proof. -/
theorem tree_capacity (r : Cube n) (edges : List (Cube n × Cube n)) (w k : ℕ)
    (hr : r.vars.card ≤ w)
    (he : ∀ e ∈ edges, e.2.vars.card ≤ w ∧
      ∃ i ∈ e.1.vars, i ∉ e.2.vars ∨ e.1.bits i ≠ e.2.bits i)
    (hk : ∀ s, starts s (events r edges) ≤ k) :
    edges.length + 2 ≤ k * 2 ^ (w+1) := by
  have hm := width_mass r edges w hr he
  rw [double_count] at hm
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Row n))) (fun s _ => hk s)
  simp [Fintype.card_pi] at hsum
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos n)
  calc
    _ ≤ _ := hm
    _ ≤ _ := Nat.mul_le_mul_right _ hsum
    _ = _ := by ac_rfl

/-- A model contributes no starts, giving a strict capacity inequality. -/
theorem sat_capacity (r : Cube n) (edges : List (Cube n × Cube n)) (w k : ℕ)
    (hr : r.vars.card ≤ w) (hkpos : 0 < k)
    (he : ∀ e ∈ edges, e.2.vars.card ≤ w ∧
      ∃ i ∈ e.1.vars, i ∉ e.2.vars ∨ e.1.bits i ≠ e.2.bits i)
    (hk : ∀ s, starts s (events r edges) ≤ k)
    (hs : ∃ s, starts s (events r edges) = 0) :
    edges.length + 2 < k * 2 ^ (w+1) := by
  obtain ⟨s, hs⟩ := hs
  have hm := width_mass r edges w hr he
  rw [double_count] at hm
  have hsum := Finset.sum_lt_sum (s := (univ : Finset (Row n)))
    (fun t _ => hk t) ⟨s, mem_univ _, hs.trans_lt hkpos⟩
  simp [Fintype.card_pi] at hsum
  apply Nat.lt_of_mul_lt_mul_right (a := 2^n)
  calc
    _ ≤ _ := hm
    _ < (2^n * k) * 2^(w+1) := Nat.mul_lt_mul_of_pos_right hsum (Nat.two_pow_pos (w+1))
    _ = (k * 2^(w+1)) * 2^n := by simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Vertices of the complete binary tree of height w, indexed by prefix length and bits. -/
abbrev Node (w : ℕ) := (d : Fin (w+1)) × (Fin d.val → Bool)

theorem node_count (w : ℕ) : Fintype.card (Node w) + 1 = 2^(w+1) := by
  have h : ∀ b : ℕ, (∑ d : Fin b, 2^d.val) + 1 = 2^b := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
      omega
  simpa [Node, Fintype.card_sigma, Fintype.card_pi] using h (w+1)

def slot (u : Node w) (i : Fin w) : Literal :=
  if h : i.val < u.1.val then (2*i.val+1, !(u.2 ⟨i.val,h⟩)) else (2*i.val, true)

def nodeClause (u : Node w) : Clause := List.ofFn (slot u)

@[simp] theorem node_width (u : Node w) : (nodeClause u).length = w := by
  simp [nodeClause]

private theorem slot_index (u : Node w) (i : Fin w) : (slot u i).1 / 2 = i.val := by
  unfold slot
  split <;> simp
  omega

theorem node_antichain (u v : Node w) (h : ∀ l ∈ nodeClause u, l ∈ nodeClause v) :
    u = v := by
  have eqs (i : Fin w) : slot u i = slot v i := by
    have hh := h (slot u i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hh
    have hij : j = i := Fin.ext ((slot_index v j).symm.trans (hj ▸ slot_index u i))
    simpa [hij] using hj.symm
  have leDepth (a b : Node w) (e : ∀ i, slot a i = slot b i) : a.1.val ≤ b.1.val := by
    by_contra! hn
    let i : Fin w := ⟨b.1.val, by have := a.1.isLt; omega⟩
    have hx := congrArg Prod.fst (e i)
    simp [slot, i, hn] at hx
  obtain ⟨d, f⟩ := u
  obtain ⟨t, g⟩ := v
  have he : d = t := Fin.ext (Nat.le_antisymm (leDepth _ _ eqs)
    (leDepth _ _ (fun i => (eqs i).symm)))
  subst t
  congr 1
  funext j
  let i : Fin w := ⟨j.val, by have := d.isLt; have := j.isLt; omega⟩
  have hh := congrArg Prod.snd (eqs i)
  simpa [slot, i, j.isLt] using hh

/-- Anchors at even variables specify the first eligible depth. Odd variables
    select the unique branch. All leaves are eligible. -/
def Eligible (w d : ℕ) (s : Assignment) : Prop :=
  ∀ i : Fin w, d ≤ i.val → s (2*i.val) = false

private theorem leaf_eligible (w : ℕ) (s : Assignment) : Eligible w w s :=
  fun i h => False.elim (Nat.not_le_of_lt i.isLt h)

noncomputable def firstDepth (w : ℕ) (s : Assignment) : ℕ := by
  classical
  exact Nat.find (show ∃ d, Eligible w d s from ⟨w,leaf_eligible w s⟩)

theorem depth_test (w d : ℕ) (s : Assignment) : Eligible w d s ↔ firstDepth w s ≤ d := by
  classical
  constructor
  · intro h
    exact Nat.find_min' (show ∃ t, Eligible w t s from ⟨w,leaf_eligible w s⟩) h
  · intro h i hi
    exact Nat.find_spec (show ∃ t, Eligible w t s from ⟨w,leaf_eligible w s⟩) i (h.trans hi)

/-- Formal trace description: exactly one address at each depth from the
    threshold through every subsequent depth, along the same branch. -/
theorem false_prefix_suffix (u : Node w) (s : Assignment) :
    (nodeClause u).eval s = false ↔ firstDepth w s ≤ u.1.val ∧
      ∀ j : Fin u.1.val, s (2*j.val+1) = u.2 j := by
  rw [← depth_test]
  have all : (nodeClause u).eval s = false ↔ ∀ i : Fin w, s (slot u i).1 ≠ (slot u i).2 := by
    simp [nodeClause, Clause.eval, Literal.eval, List.any_eq_false]
  rw [all]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [slot, Nat.not_lt.mpr hi] using h i
    · intro j
      let i : Fin w := ⟨j.val, by have := j.isLt; have := u.1.isLt; omega⟩
      simpa [slot, i, j.isLt] using h i
  · rintro ⟨he, hb⟩ i
    by_cases hi : i.val < u.1.val
    · simpa [slot, hi] using hb ⟨i.val,hi⟩
    · simpa [slot, hi] using he i (Nat.le_of_not_gt hi)

theorem leaf_removal_model (w : ℕ) :
    ∃ s : Assignment, ∃ leaf : Node w, leaf.1.val = w ∧
      ∀ u : Node w, (nodeClause u).eval s = false ↔ u = leaf := by
  let s : Assignment := fun i => decide (i % 2 = 0)
  let leaf : Node w := ⟨Fin.last w, fun _ => false⟩
  refine ⟨s, leaf, rfl, ?_⟩
  intro u
  rw [false_prefix_suffix, ← depth_test]
  constructor
  · rintro ⟨he, hb⟩
    obtain ⟨d, f⟩ := u
    have hd : d = Fin.last w := by
      apply Fin.ext
      by_contra hne
      have hdw := d.isLt
      have lt : d.val < w := by simp at hne; omega
      have bad := he ⟨d.val,lt⟩ (le_refl _)
      simp [s] at bad
    subst d
    unfold leaf
    congr 1
    funext j
    simpa [s] using (hb j).symm
  · rintro rfl
    exact ⟨leaf_eligible w s, fun j => by simp [s, leaf]⟩

/-- One added leaf has an address prefix, its parent's last address bit, and a sign
    on a fresh variable shared only within the matching port of this round. -/
abbrev Arm (t : ℕ) := (Fin t → Bool) × Bool × Bool

def guardLits (b : Fin t → Bool) : Clause :=
  List.ofFn fun i : Fin t => (2*i.val+1, !(b i))

def fresh (t r : ℕ) (port : Bool) := 2*(t+1) + 2*r + port.toNat

def armParent (a : Arm t) : Clause :=
  (2*t+1, !a.2.1) :: guardLits a.1

def armChild (r : ℕ) (a : Arm t) : Clause :=
  (fresh t r a.2.1, !a.2.2) :: guardLits a.1

private theorem guard_false (b : Fin t → Bool) (s : Assignment) :
    (guardLits b).eval s = false ↔ b = fun i => s (2*i.val+1) := by
  simp [guardLits, Clause.eval, Literal.eval, List.any_eq_false, funext_iff]
  exact forall_congr' fun _ => eq_comm

theorem arm_parent_is_leaf (a : Arm t) :
    ∃ u : Node (t+1), u.1.val = t+1 ∧
      ∀ s, (armParent a).eval s = (nodeClause u).eval s := by
  let f : Fin (t+1) → Bool := Fin.lastCases a.2.1 a.1
  let u : Node (t+1) := ⟨Fin.last (t+1),f⟩
  refine ⟨u,rfl,fun s => ?_⟩
  apply Bool.eq_iff_iff.mpr
  suffices H : (armParent a).eval s = false ↔ (nodeClause u).eval s = false by
    cases h₁ : (armParent a).eval s <;> cases h₂ : (nodeClause u).eval s <;> simp_all
  rw [false_prefix_suffix, ← depth_test]
  have hp : (armParent a).eval s = false ↔ s (2*t+1) = a.2.1 ∧
      a.1 = fun i => s (2*i.val+1) := by
    simp only [armParent, Clause.eval, List.any_cons, Bool.or_eq_false_iff]
    change (_ ∧ (guardLits a.1).eval s = false) ↔ _
    simp [guard_false, Literal.eval]
  rw [hp]
  constructor
  · rintro ⟨hs,hb⟩
    refine ⟨leaf_eligible _ _, ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [u,f] using hs
    · simpa [u,f] using congrFun hb.symm i
  · rintro ⟨_,h⟩
    exact ⟨by simpa [u,f] using h (Fin.last t),
      funext fun i => by simpa [u,f] using (h i.castSucc).symm⟩

def activeArm (t r : ℕ) (s : Assignment) : Arm t :=
  let p := !(s (2*t+1))
  (fun i => s (2*i.val+1), p, s (fresh t r p))

theorem arm_start (r : ℕ) (a : Arm t) (s : Assignment) :
    ((armChild r a).eval s = false ∧ (armParent a).eval s = true) ↔ a = activeArm t r s := by
  obtain ⟨b,p,d⟩ := a
  have hh : (armChild r (b,p,d)).eval s = false ↔
      s (fresh t r p) = d ∧ b = fun i => s (2*i.val+1) := by
    simp only [armChild, Clause.eval, List.any_cons, Bool.or_eq_false_iff]
    change (_ ∧ (guardLits b).eval s = false) ↔ _
    simp [Literal.eval, guard_false]
  rw [hh]
  by_cases hb : b = fun i : Fin t => s (2*i.val+1)
  · have hg := (guard_false b s).2 hb
    simp only [armParent, Clause.eval, List.any_cons]
    change (_ ∧ (Literal.eval s _ || (guardLits b).eval s) = true) ↔ _
    rw [hg]
    simp [activeArm, Literal.eval, hb, Prod.ext_iff]
    cases s (2*t+1) <;> cases p <;> simp <;> exact eq_comm
  · simp [activeArm, hb, Prod.ext_iff]

theorem arm_count (t : ℕ) : Fintype.card (Arm t) = 2^((t+1)+1) := by
  simp [Arm, pow_succ, Nat.mul_assoc]

def previous (u : Node w) (h : 0 < u.1.val) : Node w :=
  ⟨⟨u.1.val-1, by have := u.1.isLt; omega⟩,
   fun j => u.2 ⟨j.val, by have hj : j.val < u.1.val-1 := j.isLt; omega⟩⟩

def BaseStart (u : Node w) (s : Assignment) : Prop :=
  (nodeClause u).eval s = false ∧
    ∀ h : 0 < u.1.val, (nodeClause (previous u h)).eval s = true

private theorem base_start_test (u : Node w) (s : Assignment) :
    BaseStart u s ↔ u.1.val = firstDepth w s ∧ ∀ j : Fin u.1.val, s (2*j.val+1) = u.2 j := by
  simp only [BaseStart, false_prefix_suffix]
  constructor
  · rintro ⟨⟨hle,hbits⟩,hp⟩
    refine ⟨?_,hbits⟩
    by_contra! hn
    have h : 0 < u.1.val := by omega
    have bad : (nodeClause (previous u h)).eval s = false := by
      apply (false_prefix_suffix _ _).mpr
      exact ⟨by change _ ≤ u.1.val-1; omega,
        fun j => hbits ⟨j.val, by have := j.isLt; change j.val < u.1.val-1 at this; omega⟩⟩
    simp [hp h] at bad
  · rintro ⟨hd,hb⟩
    refine ⟨⟨hd.ge,hb⟩,fun h => ?_⟩
    by_contra! bad
    have hh := ((false_prefix_suffix (previous u h) s).mp (by simpa using bad)).1
    change _ ≤ u.1.val-1 at hh
    omega

theorem unique_base_start (w : ℕ) (s : Assignment) : ∃! u : Node w, BaseStart u s := by
  let d : Fin (w+1) := ⟨firstDepth w s,
    Nat.lt_succ_of_le ((depth_test _ _ _).mp (leaf_eligible w s))⟩
  refine ⟨⟨d,fun j => s (2*j.val+1)⟩, (base_start_test _ _).2 ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro ⟨e,f⟩ h
  have ⟨he,hf⟩ := (base_start_test _ _).1 h
  have hd : e = d := Fin.ext he
  subst e
  congr 1
  exact funext fun j => (hf j).symm

abbrev Vertex (t rounds : ℕ) := Node (t+1) ⊕ (Fin rounds × Arm t)

def vertexClause : Vertex t rounds → Clause
  | .inl u => nodeClause u
  | .inr (r,a) => armChild r a

theorem vertex_width (v : Vertex t rounds) : (vertexClause v).length = t+1 := by
  rcases v with u | ⟨r,a⟩ <;> simp [vertexClause, armChild, guardLits]

private theorem guard_low (b : Fin t → Bool) (l : Literal) (h : l ∈ guardLits b) :
    l.1 < 2*t := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  have := i.isLt
  dsimp
  omega

private theorem node_low (u : Node (t+1)) (l : Literal) (h : l ∈ nodeClause u) :
    l.1 < 2*(t+1) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  have := i.isLt
  unfold slot
  split <;> dsimp <;> omega

private theorem fresh_high (t r : ℕ) (p : Bool) : 2*(t+1) ≤ fresh t r p := by
  simp only [fresh]
  omega

private theorem arm_antichain (r z : Fin rounds) (a b : Arm t)
    (h : ∀ l ∈ armChild r a, l ∈ armChild z b) : (r,a) = (z,b) := by
  obtain ⟨f,p,d⟩ := a
  obtain ⟨g,v,e⟩ := b
  have hh := h (fresh t r p,!d) (.head ..)
  rcases List.mem_cons.mp hh with head | low
  · have hvar := congrArg Prod.fst head
    have hbit := congrArg Prod.snd head
    change fresh t r p = fresh t z v at hvar
    change (!d) = (!e) at hbit
    have same : r = z ∧ p = v := by
      cases p <;> cases v <;> simp [fresh] at hvar ⊢ <;> first | exact Fin.ext (by omega) | omega
    obtain ⟨rfl,rfl⟩ := same
    obtain rfl : d = e := by simpa using hbit
    suffices f = g by simp [this]
    funext i
    have hf : (2*i.val+1, !(f i)) ∈ guardLits f := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hg := List.mem_cons.mp (h _ (List.mem_cons_of_mem _ hf))
    rcases hg with bad | mem
    · have hv := congrArg Prod.fst bad
      change 2*i.val+1 = fresh t r p at hv
      have := i.isLt
      have := fresh_high t r p
      omega
    · obtain ⟨j,hj⟩ := List.mem_ofFn.mp mem
      have hv := congrArg Prod.fst hj
      change 2*j.val+1 = 2*i.val+1 at hv
      obtain rfl : j = i := Fin.ext (by omega)
      simpa using (congrArg Prod.snd hj).symm
  · have lo := guard_low g _ low
    change fresh t r p < 2*t at lo
    have := fresh_high t r p
    omega

theorem vertex_antichain (u v : Vertex t rounds)
    (h : ∀ l ∈ vertexClause u, l ∈ vertexClause v) : u = v := by
  rcases u with u | ⟨r,a⟩ <;> rcases v with v | ⟨z,b⟩
  · exact congrArg Sum.inl (node_antichain _ _ h)
  · let i := Fin.last t
    have hm := h (slot u i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have idx := slot_index u i
    change _ / 2 = t at idx
    rcases List.mem_cons.mp hm with hh | hg
    · have hh' := congrArg Prod.fst hh
      change (slot u i).1 = fresh t z b.2.1 at hh'
      have := fresh_high t z b.2.1
      omega
    · have := guard_low _ _ hg
      omega
  · have hh := h (fresh t r a.2.1, !a.2.2) (.head ..)
    have lo := node_low v _ hh
    change fresh t r a.2.1 < 2*(t+1) at lo
    exact False.elim ((Nat.not_lt_of_ge (fresh_high ..)) lo)
  · exact congrArg Sum.inr (arm_antichain r z a b h)

def StartsAt (s : Assignment) : Vertex t rounds → Prop
  | .inl u => BaseStart u s
  | .inr (r,a) => (armChild r a).eval s = false ∧ (armParent a).eval s = true

theorem extremal_size (t rounds : ℕ) :
    Fintype.card (Vertex t rounds) + 1 = (rounds+1) * 2^((t+1)+1) := by
  have h := node_count (t+1)
  rw [show Fintype.card (Vertex t rounds) =
    Fintype.card (Node (t+1)) + rounds * Fintype.card (Arm t) by
      change Fintype.card (Node (t+1) ⊕ (Fin rounds × Arm t)) = _
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin], arm_count]
  rw [Nat.add_mul, one_mul]
  omega

open scoped Classical in
theorem extremal_components (t rounds : ℕ) (s : Assignment) :
    ∑ v : Vertex t rounds, (if @StartsAt t rounds s v then 1 else 0 : ℕ) = rounds+1 := by
  classical
  obtain ⟨u,hu,unique⟩ := unique_base_start (t+1) s
  have test (v : Node (t+1)) : BaseStart v s ↔ v = u :=
    ⟨unique v, fun h => h ▸ hu⟩
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [StartsAt, test, arm_start, Nat.add_comm]

/-- A zero sum of squared integer residuals certifies the model count from
    any proposed polynomial in the component count. -/
theorem spectral_certificate {α : Type*} [Fintype α] (c : α → ℕ) (q : ℕ → ℤ)
    (check : ∑ s, (c s : ℤ) * (q (c s))^2 = 0) :
    (∑ s, q (c s)) = ((univ.filter (fun s => c s = 0)).card : ℤ) * q 0 := by
  have nz (s : α) (hs : c s ≠ 0) : q (c s) = 0 := by
    have pos (x : α) : 0 ≤ (c x : ℤ) * (q (c x))^2 :=
      mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => pos x)).mp check s (mem_univ _)
    have hc : (c s : ℤ) ≠ 0 := by exact_mod_cast hs
    have hh := (mul_eq_zero.mp hz).resolve_left hc
    simpa using hh
  calc
    _ = ∑ s, if c s = 0 then q 0 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : c s = 0 <;> simp [h, nz]
    _ = _ := by simp [← Finset.sum_filter]

/-- Topological vertex numbering covers every rooted clause tree after relabelling. -/
def treeStarts (cl : Fin m → Clause) (parent : Fin m → Option (Fin m)) (s : Assignment) : ℕ :=
  (univ.filter fun i => (cl i).eval s = false ∧
    ∀ p ∈ parent i, (cl p).eval s = true).card

theorem starts_zero_iff_model (cl : Fin m → Clause) (parent : Fin m → Option (Fin m))
    (before : ∀ i p, parent i = some p → p < i) (s : Assignment) :
    treeStarts cl parent s = 0 ↔ CNF.eval s (List.ofFn cl) = true := by
  classical
  have model : CNF.eval s (List.ofFn cl) = true ↔ ∀ i, (cl i).eval s = true := by
    simp [CNF.eval]
  rw [model]
  constructor
  · intro h i
    by_contra! hn
    let bad := univ.filter fun j => (cl j).eval s = false
    have hi : i ∈ bad := by simpa [bad] using hn
    let j := bad.min' ⟨i,hi⟩
    have hj : j ∈ bad := min'_mem ..
    have few : ∀ p ∈ parent j, (cl p).eval s = true := by
      intro p hp
      by_contra! hf
      have mem : p ∈ bad := by simpa [bad] using hf
      exact (not_lt_of_ge (bad.min'_le p mem)) (before j p hp)
    have jt : j ∈ univ.filter (fun v => (cl v).eval s = false ∧
        ∀ p ∈ parent v, (cl p).eval s = true) :=
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2, few⟩
    exact (Finset.card_pos.mpr ⟨j,jt⟩).ne' h
  · intro h
    simp [treeStarts, h]

/-- The certificate counts models of the repository CNF, including the empty formula. -/
theorem certified_tree_models (cl : Fin m → Clause) (parent : Fin m → Option (Fin m))
    (before : ∀ i p, parent i = some p → p < i) (n : ℕ) (q : ℕ → ℤ)
    (check : ∑ s : Row n, (treeStarts cl parent (extend s) : ℤ) *
      (q (treeStarts cl parent (extend s)))^2 = 0) :
    (∑ s : Row n, q (treeStarts cl parent (extend s))) =
      ((univ.filter (fun s : Row n => CNF.eval (extend s) (List.ofFn cl) = true)).card : ℤ)
      * q 0 := by
  simpa only [starts_zero_iff_model cl parent before] using
    spectral_certificate (fun s : Row n => treeStarts cl parent (extend s)) q check

end ClauseTrees
