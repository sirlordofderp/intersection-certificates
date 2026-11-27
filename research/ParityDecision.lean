import PEqualNP.Defs.Search
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.SetTheory.Cardinal.Finite

namespace ParityDecision

open PEqualNP.Search

abbrev Data := ℕ → Fin 3 → Literal
abbrev Ports := ℕ → Fin 3 → Bool
def slots : List (Fin 3) := [0,1,2]
def root (v : ℕ) := 3*v
def selector (i : ℕ) (j : Fin 3) := 3*(3*i+j.val)+1
def mask (i : ℕ) (j : Fin 3) := 3*(3*i+j.val)+2

def pack (x : Assignment) (u y : Ports) : Assignment := fun k =>
  let i := k/3/3
  let j : Fin 3 := ⟨k/3%3, Nat.mod_lt _ (by decide)⟩
  if k%3 = 0 then x (k/3) else if k%3 = 1 then u i j else y i j

@[simp] theorem at_root (x : Assignment) (u y : Ports) (v : ℕ) :
    pack x u y (root v) = x v := by simp [pack,root]

@[simp] theorem at_selector (x : Assignment) (u y : Ports) (i : ℕ) (j : Fin 3) :
    pack x u y (selector i j) = u i j := by
  unfold pack selector
  simp [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt j.isLt, Nat.div_eq_of_lt j.isLt,
    Nat.not_le_of_gt j.isLt]

@[simp] theorem at_mask (x : Assignment) (u y : Ports) (i : ℕ) (j : Fin 3) :
    pack x u y (mask i j) = y i j := by
  unfold pack mask
  simp [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt j.isLt, Nat.div_eq_of_lt j.isLt,
    Nat.not_le_of_gt j.isLt]

theorem pack_readback (σ : Assignment) :
    pack (fun v => σ (root v)) (fun i j => σ (selector i j))
      (fun i j => σ (mask i j)) = σ := by
  funext k
  simp only [pack,root,selector,mask]
  split_ifs <;> congr 1 <;> omega

def gate (D : Data) (i : ℕ) (j : Fin 3) : CNF :=
  let l := D i j
  [[(selector i j,false),(root l.1,l.2),(mask i j,true)],
   [(selector i j,false),(root l.1,!l.2),(mask i j,false)]]

def gadget (D : Data) (i : ℕ) : CNF :=
  (slots.map fun j => (selector i j,true)) :: slots.flatMap (gate D i)

def original (D : Data) (ids : List ℕ) : CNF := ids.map fun i => slots.map (D i)
def encoded (D : Data) (ids : List ℕ) : CNF := ids.flatMap (gadget D)
def pins (ids : List ℕ) : CNF := ids.flatMap fun i => slots.map fun j => [(mask i j,false)]

def bad (σ : Assignment) (c : Clause) : ℕ := if c.eval σ then 0 else 1
def energy (σ : Assignment) (F : CNF) : ℕ := (F.map (bad σ)).sum

def subwords : List Literal → List (List Literal)
  | [] => [[]]
  | a::t => subwords t ++ (subwords t).map (a::·)

def char (σ : Assignment) (t : List Literal) : ℤ :=
  (t.map fun l => if l.eval σ then (-1 : ℤ) else 1).prod

/-- Each signed clause has an exact integer Walsh expansion, including
    repeated variables, tautologies, and the empty clause. -/
theorem clause_spectrum (σ : Assignment) (c : Clause) :
    ((subwords c).map (char σ)).sum = 2^c.length * (bad σ c : ℤ) := by
  induction c with
  | nil => simp [subwords,char,bad,Clause.eval]
  | cons a t ih =>
    have aux (L : List (List Literal)) : (L.map (fun w => char σ (a::w))).sum =
        (if a.eval σ then (-1 : ℤ) else 1) * (L.map (char σ)).sum := by
      induction L with
      | nil => simp
      | cons w L h => simp only [List.map_cons,List.sum_cons,mul_add,← h]; rfl
    simp only [subwords,List.map_append,List.sum_append,List.map_map,Function.comp_def,
      aux,ih,List.length_cons,pow_succ]
    cases ha : a.eval σ <;> cases ht : t.any (Literal.eval σ) <;> simp [bad,Clause.eval,ha,ht]
    ring

@[simp] private theorem energy_append (σ : Assignment) (A B : CNF) :
    energy σ (A++B) = energy σ A + energy σ B := by simp [energy]

@[simp] private theorem energy_cons (σ : Assignment) (c : Clause) (F : CNF) :
    energy σ (c::F) = bad σ c + energy σ F := by simp [energy]

def twist (D : Data) (x : Assignment) (y : Ports) : Ports := fun i j =>
  (D i j).eval x ^^ y i j

/-- For fixed original bits the signed parity change is its own inverse. -/
theorem twist_involutive (D : Data) (x : Assignment) : Function.Involutive (twist D x) := by
  intro y
  funext i j
  unfold twist
  cases (D i j).eval x <;> cases y i j <;> rfl

def blockCost (u b : Fin 3 → Bool) : ℕ :=
  (if slots.any u then 0 else 1) +
    (slots.map fun j => if u j && !b j then 1 else 0).sum

private theorem gate_energy (D : Data) (i : ℕ) (j : Fin 3) (x : Assignment) (u y : Ports) :
    energy (pack x u y) (gate D i j) =
    if u i j && !(twist D x y i j) then 1 else 0 := by
  simp only [gate,energy,bad,Clause.eval,Literal.eval,List.map_cons,List.map_nil,
    List.any_cons,List.any_nil,List.sum_cons,List.sum_nil,at_root,at_mask,at_selector,twist]
  have calcGate (s m v p : Bool) :
      (if (s == false || (v == p || (m == true || false))) then 0 else 1) +
      ((if (s == false || (v == !p || (m == false || false))) then 0 else 1) + 0) =
      (if s && !((v == p) ^^ m) then 1 else 0) := by
    cases s <;> cases m <;> cases v <;> cases p <;> decide
  exact calcGate _ _ _ _

private theorem gadget_energy (D : Data) (i : ℕ) (x : Assignment) (u y : Ports) :
    energy (pack x u y) (gadget D i) = blockCost (u i) (twist D x y i) := by
  simp [gadget,slots,blockCost,gate_energy,bad,Clause.eval,Literal.eval]

/-- The complete violation-count function in independent blocks of six bits. -/
theorem encoded_energy (D : Data) (ids : List ℕ) (x : Assignment) (u y : Ports) :
    energy (pack x u y) (encoded D ids) =
    (ids.map fun i => blockCost (u i) (twist D x y i)).sum := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    simp only [encoded,List.flatMap_cons,energy_append,gadget_energy,List.map_cons,List.sum_cons]
    rw [← ih]
    rfl

private theorem good_gate (D : Data) (i : ℕ) (j : Fin 3) (σ : Assignment)
    (hz : σ (mask i j) = false) :
    (gate D i j).eval σ = true ↔
    (σ (selector i j) = true → (D i j).eval (fun v => σ (root v)) = true) := by
  simp only [gate,CNF.eval,List.all_cons,List.all_nil,Clause.eval,List.any_cons,List.any_nil,
    Literal.eval,hz]
  cases σ (selector i j) <;> cases σ (root (D i j).1) <;> cases (D i j).2 <;> decide

private theorem pins_iff (ids : List ℕ) (σ : Assignment) :
    (pins ids).eval σ = true ↔ ∀ i ∈ ids, ∀ j ∈ slots, σ (mask i j) = false := by
  simp [pins,CNF.eval,Clause.eval,Literal.eval,List.all_eq_true]

private theorem gadget_good (D : Data) (i : ℕ) (σ : Assignment)
    (hz : ∀ j ∈ slots, σ (mask i j) = false) :
    (gadget D i).eval σ = true ↔
    (∃ j ∈ slots, σ (selector i j) = true) ∧
    ∀ j ∈ slots, σ (selector i j) = true → (D i j).eval (fun v => σ (root v)) = true := by
  have h (j) (hj : j ∈ slots) := good_gate D i j σ (hz j hj)
  simp only [gadget,CNF.eval,List.all_cons,Bool.and_eq_true,List.all_flatMap,List.all_eq_true]
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨?_,fun j hj => (h j hj).1 (by simpa [CNF.eval,List.all_eq_true] using hb j hj)⟩
    simpa [Clause.eval,Literal.eval,List.any_eq_true] using ha
  · rintro ⟨ha,hb⟩
    exact ⟨by simpa [Clause.eval,Literal.eval,List.any_eq_true] using ha,
      fun j hj => by simpa [CNF.eval,List.all_eq_true] using (h j hj).2 (hb j hj)⟩

/-- For each original assignment, the pinned formula has an extension exactly
    when the original formula is true on that assignment. -/
theorem pinned_projection (D : Data) (ids : List ℕ) (x : Assignment) :
    (original D ids).eval x = true ↔ ∃ σ : Assignment,
    (∀ v, σ (root v) = x v) ∧ ((encoded D ids) ++ pins ids).eval σ = true := by
  have orig : (original D ids).eval x = true ↔
      ∀ i ∈ ids, ∃ j ∈ slots, (D i j).eval x = true := by
    simp [original,CNF.eval,Clause.eval,List.all_eq_true,List.any_eq_true]
  have enc (σ : Assignment) : ((encoded D ids) ++ pins ids).eval σ = true ↔
      (∀ i ∈ ids, (gadget D i).eval σ = true) ∧ (pins ids).eval σ = true := by
    simp [encoded,CNF.eval,List.all_eq_true]
  rw [orig]
  constructor
  · intro hx
    let u : Ports := fun i j => (D i j).eval x
    let σ := pack x u (fun _ _ => false)
    have hz : ∀ i, ∀ j ∈ slots, σ (mask i j) = false := by simp [σ]
    refine ⟨σ,by simp [σ],(enc σ).2 ⟨?_,(pins_iff ids σ).2 (fun i _ => hz i)⟩⟩
    intro i hi
    apply (gadget_good D i σ (hz i)).2
    simpa [σ,u] using hx i hi
  · rintro ⟨σ,hr,hf⟩ i hi
    obtain ⟨hg,hz⟩ := (enc σ).1 hf
    obtain ⟨⟨j,hj,hu⟩,hm⟩ := (gadget_good D i σ ((pins_iff ids σ).1 hz i hi)).1 (hg i hi)
    exact ⟨j,hj,by simpa [hr] using hm j hj hu⟩

theorem all_clauses_width_three (D : Data) (ids : List ℕ) :
    ∀ c ∈ encoded D ids, c.length = 3 := by
  simp [encoded,gadget,slots,gate]
  rintro c i _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

private theorem energy_zero_iff (σ : Assignment) (F : CNF) :
    energy σ F = 0 ↔ F.eval σ = true := by
  induction F with
  | nil => simp [energy,CNF.eval]
  | cons c F ih =>
    simp only [energy_cons,Nat.add_eq_zero_iff,ih,CNF.eval,List.all_cons,Bool.and_eq_true,bad]
    cases c.eval σ <;> simp

theorem unpinned_extension (D : Data) (ids : List ℕ) (x : Assignment) :
    ∃ σ : Assignment, (∀ v, σ (root v) = x v) ∧ (encoded D ids).eval σ = true := by
  let one : Ports := fun _ _ => true
  refine ⟨pack x one (twist D x one), by simp, (energy_zero_iff ..).1 ?_⟩
  rw [encoded_energy,twist_involutive D x one]
  induction ids with
  | nil => rfl
  | cons i ids ih => simp [one,blockCost,slots]

theorem pinned_sat_iff (D : Data) (ids : List ℕ) :
    Satisfiable (encoded D ids ++ pins ids) ↔ Satisfiable (original D ids) := by
  constructor
  · rintro ⟨σ,hσ⟩
    exact ⟨fun v => σ (root v),(pinned_projection D ids _).2 ⟨σ,fun _ => rfl,hσ⟩⟩
  · rintro ⟨x,hx⟩
    obtain ⟨σ,_,hσ⟩ := (pinned_projection D ids x).1 hx
    exact ⟨σ,hσ⟩

/-- The extendible syndromes at a cut are a translate of the intersection of
    the left and right column spans. This is the exact state space of the DP. -/
def cutEquiv {K G : Type*} [Field K] [AddCommGroup G] [Module K G]
    (P S : Submodule K G) (t a : G) (ha : a ∈ P) (hs : t-a ∈ S) :
    (P ⊓ S : Submodule K G) ≃ {x : G // x ∈ P ∧ t-x ∈ S} where
  toFun v := ⟨a+v, P.add_mem ha v.property.1, by
    rw [show t-(a+v) = (t-a)-v by abel]
    exact S.sub_mem hs v.property.2⟩
  invFun v := ⟨v-a, P.sub_mem v.property.1 ha, by
    rw [show (v : G)-a = (t-a)-(t-v) by abel]
    exact S.sub_mem hs v.property.2⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp

theorem cut_card {K G : Type*} [Field K] [AddCommGroup G] [Module K G]
    (P S : Submodule K G) (t a : G) (ha : a ∈ P) (hs : t-a ∈ S) :
    Nat.card {x : G // x ∈ P ∧ t-x ∈ S} = Nat.card (P ⊓ S : Submodule K G) :=
  Nat.card_congr (cutEquiv P S t a ha hs).symm

section DynamicProgram
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
abbrev Table (G : Type*) := Finset (G × ℤ)

def combine (L R : Table G) : Table G :=
  (L ×ˢ R).image fun (a,b) => (a.1+b.1,a.2+b.2)

def cheapest (T : Table G) : Table G :=
  T.filter fun a => ∀ b ∈ T, b.1 = a.1 → a.2 ≤ b.2

private def Represents (D T : Table G) : Prop :=
  D ⊆ T ∧ ∀ b ∈ T, ∃ a ∈ D, a.1 = b.1 ∧ a.2 ≤ b.2

omit [AddCommGroup G] in
private theorem cheapest_rep (T : Table G) : Represents (cheapest T) T := by
  refine ⟨Finset.filter_subset ..,?_⟩
  intro b hb
  let F := T.filter fun a => a.1 = b.1
  have hf : b ∈ F := Finset.mem_filter.mpr ⟨hb,rfl⟩
  obtain ⟨a,ha,hmin⟩ := F.exists_min_image Prod.snd ⟨b,hf⟩
  obtain ⟨hat,heq⟩ := Finset.mem_filter.mp ha
  exact ⟨a,Finset.mem_filter.mpr ⟨hat,fun c hc he => hmin c
    (Finset.mem_filter.mpr ⟨hc,he.trans heq⟩)⟩,heq,hmin b hf⟩

private theorem step_rep {D T : Table G} (h : Represents D T) (R : Table G) :
    Represents (cheapest (combine D R)) (combine T R) := by
  have small := cheapest_rep (combine D R)
  constructor
  · intro z hz
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp (small.1 hz)
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨h.1 ha,hb⟩,rfl⟩
  · intro z hz
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨c,hc,hs,hle⟩ := h.2 a ha
    have entry : (c.1+b.1,c.2+b.2) ∈ combine D R :=
      Finset.mem_image.mpr ⟨(c,b),Finset.mem_product.mpr ⟨hc,hb⟩,rfl⟩
    obtain ⟨q,hq,he,hcost⟩ := small.2 _ entry
    exact ⟨q,hq,he.trans (congrArg (·+b.1) hs),hcost.trans (add_le_add_left hle _)⟩

def allCosts : List (Table G) → Table G
  | [] => {(0,0)}
  | r::rs => combine (allCosts rs) r

def minCosts : List (Table G) → Table G
  | [] => {(0,0)}
  | r::rs => cheapest (combine (minCosts rs) r)

/-- Retaining only the minimum cost per syndrome preserves every decision
    threshold, including when individual block costs are negative. -/
theorem trellis_threshold (blocks : List (Table G)) (target : G) (k : ℤ) :
    (∃ c ≤ k, (target,c) ∈ allCosts blocks) ↔ ∃ c ≤ k, (target,c) ∈ minCosts blocks := by
  have rep : Represents (minCosts blocks) (allCosts blocks) := by
    induction blocks with
    | nil => exact ⟨fun _ h => h,fun a ha => ⟨a,ha,rfl,le_rfl⟩⟩
    | cons r rs ih => exact step_rep ih r
  constructor
  · rintro ⟨c,hk,hc⟩
    obtain ⟨⟨s,t⟩,ht,hs,hle⟩ := rep.2 _ hc
    change s = target at hs
    exact ⟨t,hle.trans hk,hs ▸ ht⟩
  · rintro ⟨c,hk,hc⟩
    exact ⟨c,hk,rep.1 hc⟩
end DynamicProgram

/-- After normalizing literal signs, the two sides of an occurrence-consistency
    constraint may be joined exactly when their shared original bits agree. -/
def futures (A B : Finset ℕ) (l : A → Bool) : Set (B → Bool) :=
  {r | ∀ i (ha : i ∈ A) (hb : i ∈ B), l ⟨i,ha⟩ = r ⟨i,hb⟩}

/-- Exact number of distinct continuation sets for the pinned occurrence data.
    Observations inside a block are unrestricted here; clause costs are optimized
    by the trellis separately. -/
theorem shared_variable_states (A B : Finset ℕ) :
    Nat.card (Set.range (futures A B)) = 2^(A ∩ B).card := by
  classical
  let code (v : (A ∩ B : Finset ℕ) → Bool) : Set (B → Bool) :=
    {r | ∀ i : (A ∩ B : Finset ℕ), v i = r ⟨i,(Finset.mem_inter.mp i.property).2⟩}
  have inj : Function.Injective code := by
    intro u v eq
    let r : B → Bool := fun i => if h : (i : ℕ) ∈ A then
      u ⟨i,Finset.mem_inter.mpr ⟨h,i.property⟩⟩ else false
    have hu : r ∈ code u := by
      intro i
      simp [r,(Finset.mem_inter.mp i.property).1]
    rw [eq] at hu
    funext i
    simpa [r,(Finset.mem_inter.mp i.property).1] using (hu i).symm
  have im : Set.range (futures A B) = Set.range code := by
    ext s
    constructor
    · rintro ⟨l,rfl⟩
      refine ⟨fun i => l ⟨i,(Finset.mem_inter.mp i.property).1⟩,?_⟩
      ext r
      exact ⟨fun h i ha hb => h ⟨i,Finset.mem_inter.mpr ⟨ha,hb⟩⟩,
        fun h i => h i (Finset.mem_inter.mp i.property).1 (Finset.mem_inter.mp i.property).2⟩
    · rintro ⟨u,rfl⟩
      let l : A → Bool := fun i => if h : (i : ℕ) ∈ B then
        u ⟨i,Finset.mem_inter.mpr ⟨i.property,h⟩⟩ else false
      refine ⟨l,?_⟩
      ext r
      constructor
      · intro h i
        have := h i (Finset.mem_inter.mp i.property).1 (Finset.mem_inter.mp i.property).2
        simpa [l,(Finset.mem_inter.mp i.property).2] using this
      · intro h i ha hb
        simpa [l,hb] using h ⟨i,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
  rw [im,← Nat.card_congr (Equiv.ofInjective code inj),Nat.card_fun]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Fintype.card_bool,Fintype.card_coe]

end ParityDecision
