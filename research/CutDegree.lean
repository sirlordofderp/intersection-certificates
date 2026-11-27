import ClauseTrees
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace CutDegree

variable {V : Type*}
abbrev Fn (V : Type*) := (V → Bool) → ℚ

def bit (i : V) : Fn V := fun x => if x i then 1 else 0
def cut (i j : V) : Fn V := fun x => if x i && !x j then 1 else 0
def low : V → Bool := fun _ => false
def high : V → Bool := fun _ => true
def K (c : ℚ) : Fn V := fun _ => c

def cuts (E : V → V → Prop) : Set (Fn V) :=
  {f | ∃ i j, E i j ∧ f = cut i j}
def reads (H : Set (Fn V)) : Set (Fn V) :=
  {f | f ∈ H ∨ ∃ i, f = bit i}

/-- Rational polynomials of degree at most d in the indicated generators. -/
def space (H : Set (Fn V)) (d : ℕ) : Submodule ℚ (Fn V) :=
  Submodule.span ℚ {f | ∃ l : List (Fn V), l.length ≤ d ∧ (∀ g ∈ l, g ∈ H) ∧ f = l.prod}

private theorem word_mem {H : Set (Fn V)} (l : List (Fn V)) (hl : l.length ≤ d)
    (hc : ∀ g ∈ l, g ∈ H) : l.prod ∈ space H d :=
  Submodule.subset_span ⟨l,hl,hc,rfl⟩

private theorem one_mem (H : Set (Fn V)) (d : ℕ) : (1 : Fn V) ∈ space H d :=
  word_mem [] (Nat.zero_le _) (by simp)

private theorem const_mem (H : Set (Fn V)) (d : ℕ) (c : ℚ) : K c ∈ space H d := by
  convert (space H d).smul_mem c (one_mem H d) using 1
  ext x
  simp [K]

private theorem atom {H : Set (Fn V)} {f : Fn V} (hf : f ∈ H) : f ∈ space H 1 := by
  simpa using word_mem [f] (le_refl _) (by simpa using hf : ∀ g ∈ [f], g ∈ H)

private theorem liftSpace {H J : Set (Fn V)} (h : H ⊆ J) (hk : k ≤ d) :
    space H k ≤ space J d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hl,hc,rfl⟩
  exact word_mem l (hl.trans hk) (fun g hg => h (hc g hg))

private theorem multiply {H : Set (Fn V)} {f g : Fn V} (hf : f ∈ space H k)
    (hg : g ∈ space H d) : f*g ∈ space H (k+d) := by
  induction hf,hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
    obtain ⟨l,hl,hc,rfl⟩ := hf
    obtain ⟨t,ht,he,rfl⟩ := hg
    rw [← List.prod_append]
    exact word_mem _ (by simp; omega) (fun a ha => (List.mem_append.mp ha).elim (hc a) (he a))
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ a b => rw [add_mul]; exact Submodule.add_mem _ a b
  | add_right _ _ _ _ _ _ a b => rw [mul_add]; exact Submodule.add_mem _ a b
  | smul_left c _ _ _ _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  | smul_right c _ _ _ _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

private theorem cut_mem {E : V → V → Prop} (h : E i j) : cut i j ∈ space (cuts E) 1 :=
  atom ⟨i,j,h,rfl⟩

private theorem delta_edge {E : V → V → Prop} (sym : ∀ i j, E i j → E j i) (h : E i j) :
    bit i-bit j ∈ space (cuts E) 1 := by
  have eq : bit i-bit j = cut i j-cut j i := by
    funext x
    cases hj : x j <;> cases hi : x i <;> simp [bit,cut,hi,hj]
  rw [eq]
  exact Submodule.sub_mem _ (cut_mem h) (cut_mem (sym _ _ h))

private theorem delta {E : V → V → Prop} (sym : ∀ i j, E i j → E j i)
    (p : Relation.ReflTransGen E i j) : bit i-bit j ∈ space (cuts E) 1 := by
  induction p with
  | refl => simp
  | @tail j k _ h ih =>
    rw [show bit i-bit k = (bit i-bit j)+(bit j-bit k) by ring]
    exact Submodule.add_mem _ ih (delta_edge sym h)

/-- Disagreement generators vanish at consensus, pin a true bit on their
    support, and recover every difference of vertex bits at degree one. -/
structure Pinned (H : Set (Fn V)) : Prop where
  vanish : ∀ g ∈ H, g low = 0 ∧ g high = 0
  pin : ∀ g ∈ H, ∃ i, ∀ x, g x ≠ 0 → x i = true
  difference : ∀ i j, bit i - bit j ∈ space H 1

private theorem endpoints {H : Set (Fn V)} (P : Pinned H) {f : Fn V} (hf : f ∈ space H d) :
    f low = f high := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l,_,hc,rfl⟩ := h
    induction l with
    | nil => rfl
    | cons g t _ =>
      obtain ⟨h₀,h₁⟩ := P.vanish g (hc g (.head ..))
      simp [List.prod_cons,h₀,h₁]
  | zero => rfl
  | add _ _ _ _ a b => simp [a,b]
  | smul c _ _ h => simp [h]

/-- On any nonempty product of cuts, the source of its first cut is pinned
    to true. A path difference can therefore supply the reference bit. -/
private theorem anchored {H : Set (Fn V)} (P : Pinned H) (r : V) {f : Fn V}
    (hf : f ∈ space H d) :
    bit r * (f - K (f low)) ∈ space H (d+1) := by
  induction hf using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨l,hl,hc,rfl⟩ := hw
    cases l with
    | nil =>
      have he : (1 : Fn V) - K ((1 : Fn V) low) = 0 := by ext; simp [K]
      change bit r * ((1 : Fn V) - K ((1 : Fn V) low)) ∈ _
      rw [he,mul_zero]
      exact Submodule.zero_mem _
    | cons g t =>
      have hw := word_mem (g::t) hl hc
      have h₀ := (P.vanish g (hc g (.head ..))).1
      obtain ⟨i,hi⟩ := P.pin g (hc g (.head ..))
      let word := (g :: t).prod
      have eq : bit r * (word - K (word low)) = word * ((bit r-bit i)+1) := by
        funext x
        simp only [word,List.prod_cons,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.one_apply,K,h₀,
          zero_mul,sub_zero]
        by_cases hz : g x = 0
        · simp [hz]
        · rw [show bit i x = 1 by simp [bit,hi x hz]]
          ring
      rw [eq]
      exact multiply hw ((space _ _).add_mem (P.difference r i) (one_mem _ _))
  | zero =>
    change bit r * (0 - (0 : Fn V)) ∈ _
    simp
  | add f g _ _ a b =>
    convert (space _ _).add_mem a b using 1
    ext x
    simp [K]
    ring
  | smul c f _ h =>
    convert (space _ _).smul_mem c h using 1
    ext x
    simp [K]
    ring

private def Split (H : Set (Fn V)) (r : V) (d : ℕ) (f : Fn V) : Prop :=
  ∃ a : Fn V, a ∈ space H d ∧ ∃ c : ℚ, f = a + c • bit r

private theorem split_mul {H : Set (Fn V)} (P : Pinned H) {r : V} (hk : 0 < k) (hd : 0 < d)
    (hf : Split H r k f) (hg : Split H r d g) : Split H r (k+d) (f*g) := by
  obtain ⟨a,ha,c,rfl⟩ := hf
  obtain ⟨b,hb,e,rfl⟩ := hg
  have h₁ := anchored P r ha
  have h₂ := anchored P r hb
  let A := space H (k+d)
  refine ⟨a*b + e • (bit r * (a - K (a low))) + c • (bit r * (b - K (b low))), ?_,
    e*a low + c*b low + c*e, ?_⟩
  · exact A.add_mem (A.add_mem (multiply ha hb) (A.smul_mem _ (liftSpace (by rfl) (by omega) h₁)))
      (A.smul_mem _ (liftSpace (by rfl) (by omega) h₂))
  · funext x
    cases h : x r <;> simp [bit,K,h]
    ring

private theorem split_read {H : Set (Fn V)} (P : Pinned H) (r : V) {f : Fn V} (h : f ∈ reads H) :
    Split H r 1 f := by
  rcases h with h | ⟨i,rfl⟩
  · exact ⟨f,atom h,0,by simp⟩
  · exact ⟨bit i-bit r,P.difference i r,1,by simp⟩

private theorem split_word {H : Set (Fn V)} (P : Pinned H) (r : V) (l : List (Fn V))
    (h : ∀ f ∈ l, f ∈ reads H) : Split H r l.length l.prod := by
  induction l with
  | nil => exact ⟨1,one_mem _ _,0,by simp⟩
  | cons g t ih =>
    have hg := split_read P r (h g (.head ..))
    cases t with
    | nil => simpa using hg
    | cons f l =>
      have ht := ih (fun x hx => h x (.tail _ hx))
      simpa [Nat.add_comm,List.prod_cons] using split_mul P (by decide : 0 < 1)
        (by simp : 0 < (f::l).length) hg ht

private theorem split_full {H : Set (Fn V)} (P : Pinned H) (r : V) {f : Fn V}
    (hf : f ∈ space (reads H) d) : Split H r d f := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l,hl,hc,rfl⟩ := h
    obtain ⟨a,ha,c,he⟩ := split_word P r l hc
    exact ⟨a,liftSpace (by rfl) hl ha,c,he⟩
  | zero => exact ⟨0,Submodule.zero_mem _,0,by simp⟩
  | add _ _ _ _ h₁ h₂ =>
    obtain ⟨a,ha,c,rfl⟩ := h₁
    obtain ⟨b,hb,e,rfl⟩ := h₂
    exact ⟨a+b,Submodule.add_mem _ ha hb,c+e,by rw [add_smul]; ac_rfl⟩
  | smul t _ _ ih =>
    obtain ⟨a,ha,c,rfl⟩ := ih
    exact ⟨t • a,Submodule.smul_mem _ _ ha,t*c,by rw [smul_add,mul_smul]⟩

/-- The exact observable part of the full endpoint polynomial space at every
    degree: the only additional equation identifies the two constant rows. -/
theorem pinned_observable_iff {H : Set (Fn V)} (P : Pinned H) (r : V) (d : ℕ) (f : Fn V) :
    f ∈ space H d ↔ f ∈ space (reads H) d ∧ f low = f high := by
  constructor
  · intro hf
    exact ⟨liftSpace (fun _ h => Or.inl h) (le_refl _) hf,endpoints P hf⟩
  · rintro ⟨hf,he⟩
    obtain ⟨a,ha,c,rfl⟩ := split_full P r hf
    have h := endpoints P ha
    simp [bit,low,high] at he
    have hx : c = 0 := by
      change a low = a high + c at he
      rw [h] at he
      exact (add_eq_left.mp he.symm)
    simpa [hx] using ha

/-- Both orientations of each edge on a connected graph satisfy the hypotheses. -/
theorem graph_pinned {E : V → V → Prop} (sym : ∀ i j, E i j → E j i)
    (paths : ∀ i j, Relation.ReflTransGen E i j) : Pinned (cuts E) where
  vanish := by
    rintro _ ⟨i,j,_,rfl⟩
    simp [cut,low,high]
  pin := by
    rintro _ ⟨i,j,_,rfl⟩
    refine ⟨i,?_⟩
    intro x h
    cases hi : x i <;> simp_all [cut]
  difference := fun i j => delta sym (paths i j)

theorem observable_iff {E : V → V → Prop} (sym : ∀ i j, E i j → E j i)
    (paths : ∀ i j, Relation.ReflTransGen E i j) (r : V) (d : ℕ) (f : Fn V) :
    f ∈ space (cuts E) d ↔ f ∈ space (reads (cuts E)) d ∧ f low = f high :=
  pinned_observable_iff (graph_pinned sym paths) r d f

def restrict (s : Finset V) (x : V → Bool) : s → Bool := fun i => x i

noncomputable def pattern (s : Finset V) (p : s → Bool) : Fn V := by
  classical exact fun x => if restrict s x = p then 1 else 0

def disagreement (B : Set (Finset V)) : Set (Fn V) :=
  {g | ∃ s ∈ B, ∃ p : s → Bool,
    p ≠ (fun _ => false) ∧ p ≠ (fun _ => true) ∧ g = pattern s p}

/-- Each scope pattern is an ordinary signed clause falsification flag in
    the upstream CNF semantics. Its width is the scope size. -/
theorem pattern_is_clause {n : ℕ} (s : Finset (Fin n)) (p : s → Bool) :
    ∃ c : PEqualNP.Search.Clause, c.length = s.card ∧ ∀ x,
      pattern s p x = if c.eval (ClauseTrees.extend x) then 0 else 1 := by
  classical
  let cube : ClauseTrees.Cube n := ⟨s,fun i => if h : i ∈ s then p ⟨i,h⟩ else false⟩
  refine ⟨cube.clause,by simp [ClauseTrees.Cube.clause,cube],?_⟩
  intro x
  have eq : cube.clause.eval (ClauseTrees.extend x) = false ↔ restrict s x = p := by
    rw [ClauseTrees.clause_false, ClauseTrees.mem_rows]
    constructor
    · intro h
      funext i
      simpa [cube,restrict,i.property] using h i i.property
    · intro h i hi
      simpa [cube,hi,restrict] using congrFun h ⟨i,hi⟩
  cases h : cube.clause.eval (ClauseTrees.extend x) <;> simp_all [pattern]

def adjacent (B : Set (Finset V)) (i j : V) : Prop := ∃ s ∈ B, i ∈ s ∧ j ∈ s

private theorem local_zero {B : Set (Finset V)} {s : Finset V} (hs : s ∈ B)
    (w : (s → Bool) → ℚ) (h₀ : w (fun _ => false) = 0) (h₁ : w (fun _ => true) = 0) :
    (fun x => w (restrict s x)) ∈ space (disagreement B) 1 := by
  classical
  have eq : (fun x => w (restrict s x)) = ∑ p : s → Bool, w p • pattern s p := by
    funext x
    simp [Finset.sum_apply,pattern,smul_eq_mul,mul_ite]
  rw [eq]
  apply Submodule.sum_mem
  intro p _
  by_cases a : p = (fun _ => false)
  · simp [a,h₀]
  by_cases b : p = (fun _ => true)
  · simp [b,h₁]
  exact Submodule.smul_mem _ _ (atom ⟨s,hs,p,a,b,rfl⟩)

private theorem local_difference {B : Set (Finset V)} (h : adjacent B i j) :
    bit i - bit j ∈ space (disagreement B) 1 := by
  obtain ⟨s,hs,hi,hj⟩ := h
  exact local_zero hs (fun p => bit (⟨i,hi⟩ : s) p - bit (⟨j,hj⟩ : s) p)
    (by simp [bit]) (by simp [bit])

/-- All nonmonochromatic local patterns on a connected hypergraph form a pinned family. -/
theorem hypergraph_pinned {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) : Pinned (disagreement B) where
  vanish := by
    classical
    rintro _ ⟨s,_,p,h₀,h₁,rfl⟩
    exact ⟨ite_eq_right (Ne.symm h₀), ite_eq_right (Ne.symm h₁)⟩
  pin := by
    classical
    rintro _ ⟨s,_,p,h₀,_,rfl⟩
    have hi : ∃ i, p i = true := by
      by_contra! h
      exact h₀ (funext fun i => by simpa using h i)
    obtain ⟨i,hi⟩ := hi
    refine ⟨i,?_⟩
    intro x hx
    by_cases he : restrict s x = p
    · exact (congrFun he i).trans hi
    · simp [pattern,he] at hx
  difference := by
    intro i j
    induction paths i j with
    | refl => simp
    | @tail j k _ h ih =>
      rw [show bit i-bit k = (bit i-bit j)+(bit j-bit k) by ring]
      exact Submodule.add_mem _ ih (local_difference h)

/-- A table on one nonempty scope costs one read, including both monochromatic patterns. -/
theorem local_table_mem {B : Set (Finset V)} {s : Finset V} (hs : s ∈ B)
    (v : s) (w : (s → Bool) → ℚ) :
    (fun x => w (restrict s x)) ∈ space (reads (disagreement B)) 1 := by
  let a := w (fun _ => false)
  let b := w (fun _ => true) - a
  let z := fun p : s → Bool => w p - (a + b * bit v p)
  have hz := local_zero hs z (by simp [z,bit,a]) (by simp [z,bit,b])
  have hv : bit (v : V) ∈ space (reads (disagreement B)) 1 := atom (Or.inr ⟨_,rfl⟩)
  have hm := (space (reads (disagreement B)) 1).add_mem
    (liftSpace (fun _ h => Or.inl h) (le_refl _) hz)
    ((space _ _).add_mem (const_mem _ _ a) ((space _ _).smul_mem b hv))
  convert hm using 1
  funext x
  change w (restrict s x) = (w (restrict s x) - (a + b * bit v (restrict s x))) +
    (a + b * bit (v : V) x)
  change w (restrict s x) = (_ - (a + b * bit (v : V) x)) + _
  ring

def tables (B : Set (Finset V)) : Set (Fn V) :=
  {f | ∃ s ∈ B, ∃ w : (s → Bool) → ℚ, f = fun x => w (restrict s x)}

private theorem replace_atoms {H J : Set (Fn V)} (h : ∀ f ∈ H, f ∈ space J 1) (d : ℕ) :
    space H d ≤ space J d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hl,hc,rfl⟩
  apply liftSpace (by rfl) hl
  clear hl
  induction l with
  | nil => exact one_mem _ _
  | cons g t ih =>
    simpa [Nat.add_comm] using multiply (h g (hc g (.head ..))) (ih (fun f hf => hc f (.tail _ hf)))

/-- Products of arbitrary local tables at the same degree give exactly the
    enriched space. Every variable occurs in some scope. -/
theorem table_space_eq {B : Set (Finset V)} (cover : ∀ i, ∃ s ∈ B, i ∈ s) (d : ℕ) :
    space (tables B) d = space (reads (disagreement B)) d := by
  classical
  apply le_antisymm
  · apply replace_atoms
    rintro _ ⟨s,hs,w,rfl⟩
    by_cases he : s.Nonempty
    · obtain ⟨i,hi⟩ := he
      exact local_table_mem hs ⟨i,hi⟩ w
    · have eq : (fun x => w (restrict s x)) = K (w (fun _ => false)) := by
        funext x
        apply congrArg w
        funext i
        exact (he ⟨i,i.property⟩).elim
      rw [eq]
      exact const_mem _ _ _
  · apply liftSpace _ (le_refl _)
    rintro f (⟨s,hs,p,_,_,rfl⟩ | ⟨i,rfl⟩)
    · exact ⟨s,hs,fun u => if u = p then 1 else 0,rfl⟩
    · obtain ⟨s,hs,hi⟩ := cover i
      exact ⟨s,hs,bit (⟨i,hi⟩ : s),rfl⟩

theorem hypergraph_observable_iff {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) (r : V) (d : ℕ) (f : Fn V) :
    f ∈ space (disagreement B) d ↔ f ∈ space (reads (disagreement B)) d ∧ f low = f high :=
  pinned_observable_iff (hypergraph_pinned paths) r d f

theorem disagreement_iff_local_tables {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) (cover : ∀ i, ∃ s ∈ B, i ∈ s)
    (r : V) (d : ℕ) (f : Fn V) :
    f ∈ space (disagreement B) d ↔ f ∈ space (tables B) d ∧ f low = f high := by
  rw [table_space_eq cover]
  exact hypergraph_observable_iff paths r d f

/-- The common zero set of the clause flags is precisely the two consensus rows. -/
theorem common_zero_iff {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) (r : V) (x : V → Bool) :
    (∀ g ∈ disagreement B, g x = 0) ↔ x = low ∨ x = high := by
  classical
  constructor
  · intro h
    have edge {i j : V} (he : adjacent B i j) : x i = x j := by
      obtain ⟨s,hs,hi,hj⟩ := he
      have hc : restrict s x = (fun _ => false) ∨ restrict s x = (fun _ => true) := by
        by_contra! hn
        have := h (pattern s (restrict s x)) ⟨s,hs,restrict s x,hn.1,hn.2,rfl⟩
        simp [pattern] at this
      rcases hc with e | e <;> exact (congrFun e ⟨i,hi⟩).trans (congrFun e ⟨j,hj⟩).symm
    have hall (i : V) : x r = x i := by
      induction paths r i with
      | refl => rfl
      | tail _ he ih => exact ih.trans (edge he)
    cases hr : x r with
    | false => exact Or.inl (funext fun i => (hall i).symm.trans hr)
    | true => exact Or.inr (funext fun i => (hall i).symm.trans hr)
  · rintro (rfl | rfl) g hg
    · exact ((hypergraph_pinned paths).vanish g hg).1
    · exact ((hypergraph_pinned paths).vanish g hg).2

def Covers (B : Set (Finset V)) (d : ℕ) : Prop :=
  ∃ l : List (Finset V), l.length ≤ d ∧ (∀ s ∈ l, s ∈ B) ∧ ∀ i, ∃ s ∈ l, i ∈ s

noncomputable def point (v : V → Bool) : Fn V := by
  classical exact fun x => if x = v then 1 else 0

noncomputable def consensus (V : Type*) : Fn V := point low + point high

private theorem point_of_cover {B : Set (Finset V)} (h : Covers B d) (b : Bool) :
    point (fun _ => b) ∈ space (reads (disagreement B)) d := by
  classical
  obtain ⟨l,hl,hB,hcover⟩ := h
  let test := fun s : Finset V => pattern s (fun _ => b)
  have hm (s : Finset V) (hs : s ∈ B) : test s ∈ space (reads (disagreement B)) 1 := by
    by_cases he : s.Nonempty
    · obtain ⟨i,hi⟩ := he
      exact local_table_mem hs ⟨i,hi⟩ (fun p => if p = (fun _ => b) then 1 else 0)
    · have eq : test s = 1 := by
        ext x
        have hp : restrict s x = fun _ => b := by
          funext i
          exact (he ⟨i,i.property⟩).elim
        simp [test,pattern,hp]
      rw [eq]
      exact one_mem _ _
  have prod_mem (t : List (Finset V)) (ht : ∀ s ∈ t, s ∈ B) :
      (t.map test).prod ∈ space (reads (disagreement B)) t.length := by
    induction t with
    | nil => exact one_mem _ _
    | cons s t ih =>
      simpa [Nat.add_comm] using multiply (hm s (ht s (.head ..))) (ih (fun z hz => ht z (.tail _ hz)))
  have eval (t : List (Finset V)) (x : V → Bool) :
      (t.map test).prod x = if ∀ s ∈ t, restrict s x = fun _ => b then 1 else 0 := by
    induction t with
    | nil => simp
    | cons s t ih =>
      by_cases hs : restrict s x = fun _ => b <;> simp [test,pattern,hs,ih,List.prod_cons]
  have eq : point (fun _ => b) = (l.map test).prod := by
    funext x
    rw [eval]
    have iff : (∀ s ∈ l, restrict s x = fun _ => b) ↔ x = fun _ => b := by
      constructor
      · intro hall
        funext i
        obtain ⟨s,hs,hi⟩ := hcover i
        exact congrFun (hall s hs) ⟨i,hi⟩
      · rintro rfl s _
        rfl
    simp [point,iff]
  rw [eq]
  exact liftSpace (by rfl) hl (prod_mem l hB)

private theorem word_scopes {B : Set (Finset V)} (l : List (Fn V))
    (h : ∀ g ∈ l, g ∈ disagreement B) :
    ∃ t : List (Finset V), t.length = l.length ∧ (∀ s ∈ t, s ∈ B) ∧
      ∀ x y : V → Bool, (∀ s ∈ t, restrict s x = restrict s y) → l.prod x = l.prod y := by
  induction l with
  | nil => exact ⟨[],rfl,by simp,fun _ _ _ => rfl⟩
  | cons g l ih =>
    obtain ⟨s,hs,p,_,_,rfl⟩ := h g (.head ..)
    obtain ⟨t,ht,hB,hh⟩ := ih (fun z hz => h z (.tail _ hz))
    refine ⟨s::t,by simp [ht],by simpa using And.intro hs hB,?_⟩
    intro x y hxy
    simp only [List.prod_cons,Pi.mul_apply,pattern,hxy s (.head ..),
      hh x y (fun u hu => hxy u (.tail _ hu))]

private noncomputable def sign [Fintype V] (x : V → Bool) : ℚ :=
  ∏ i, if x i then -1 else 1

private noncomputable def top [Fintype V] (f : Fn V) : ℚ := by
  classical exact ∑ x, sign x * f x

private theorem top_zero [Fintype V] (i : V) (f : Fn V)
    (h : ∀ x y, (∀ j, j ≠ i → x j = y j) → f x = f y) : top f = 0 := by
  classical
  let flip (x : V → Bool) := Function.update x i (!x i)
  have outside (x : V → Bool) (j : V) (hj : j ≠ i) : flip x j = x j :=
    Function.update_of_ne hj ..
  have inv : Function.Involutive flip := by
    intro x
    ext j
    by_cases e : j = i
    · subst j
      simp [flip]
    · rw [outside _ _ e,outside _ _ e]
  have neg (x : V → Bool) : sign (flip x) = - sign x := by
    let term := fun (x : V → Bool) (j : V) => if x j then (-1 : ℚ) else 1
    have erase : (∏ j ∈ Finset.univ.erase i, term (flip x) j) =
        ∏ j ∈ Finset.univ.erase i, term x j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [term,outside _ _ (Finset.ne_of_mem_erase hj)]
    change (∏ j, term (flip x) j) = -(∏ j, term x j)
    rw [← Finset.mul_prod_erase Finset.univ (term (flip x)) (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ (term x) (Finset.mem_univ i),erase]
    cases e : x i <;> simp [term,flip,e]
  have swap : (∑ x, sign (flip x) * f (flip x)) = top f :=
    Finset.sum_equiv inv.toPerm (by simp) (fun _ _ => rfl)
  have changeSign : (∑ x, sign (flip x) * f (flip x)) = -top f := by
    rw [top,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [neg,h _ _ (outside x),neg_mul]
  change (∑ x, sign (flip x) * f (flip x)) = top f at swap
  rw [changeSign] at swap
  exact eq_zero_of_neg_eq swap

private theorem no_cover_top [Fintype V] {B : Set (Finset V)} (hn : ¬ Covers B d)
    {f : Fn V} (hf : f ∈ space (disagreement B) d) : top f = 0 := by
  classical
  induction hf using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨l,hl,hc,rfl⟩ := hw
    obtain ⟨t,ht,hB,hh⟩ := word_scopes l hc
    have missing : ∃ i, ∀ s ∈ t, i ∉ s := by
      by_contra! h
      exact hn ⟨t,ht ▸ hl,hB,h⟩
    obtain ⟨i,hi⟩ := missing
    apply top_zero i
    intro x y hxy
    apply hh
    intro s hs
    funext j
    exact hxy j (fun e => hi s hs (e ▸ j.property))
  | zero => simp [top]
  | add _ _ _ _ ha hb => simpa [top,mul_add,Finset.sum_add_distrib] using congrArg₂ (·+·) ha hb
  | smul c f _ h =>
    change (∑ x, sign x * (c * f x)) = 0
    simp_rw [mul_left_comm (sign _) c]
    rw [← Finset.mul_sum,show (∑ x, sign x * f x) = 0 from h,mul_zero]

/-- On an even nonempty vertex set, minimum disagreement degree of consensus is
    exactly minimum hyperedge cover size. The cover is allowed to use overlaps. -/
theorem consensus_iff_cover [Fintype V] {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) (r : V)
    (heven : Even (Fintype.card V)) (d : ℕ) :
    consensus V ∈ space (disagreement B) d ↔ Covers B d := by
  classical
  have atPoint (v : V → Bool) : top (point v) = sign v := by
    simp [top,point,mul_ite]
  have nz : top (consensus V) ≠ 0 := by
    change (∑ x, sign x * (point low x + point high x)) ≠ 0
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,show (∑ x, sign x * point low x) = _ from atPoint low,
      show (∑ x, sign x * point high x) = _ from atPoint high]
    simp [sign,low,high,heven.neg_one_pow]
    norm_num
  constructor
  · intro hf
    by_contra hn
    exact nz (no_cover_top hn hf)
  · intro hc
    apply (hypergraph_observable_iff paths r d _).2
    refine ⟨(space _ _).add_mem (point_of_cover hc false) (point_of_cover hc true),?_⟩
    have neq : (low : V → Bool) ≠ high := fun h => Bool.false_ne_true (congrFun h r)
    simp [consensus,point,neq,Ne.symm neq]

private def joinScopes [DecidableEq V] : List (Finset V) → Finset V
  | [] => ∅
  | s::t => s ∪ joinScopes t

private theorem in_join [DecidableEq V] (i : V) (l : List (Finset V)) :
    i ∈ joinScopes l ↔ ∃ s ∈ l, i ∈ s := by
  induction l with
  | nil => simp [joinScopes]
  | cons s l ih => simp [joinScopes,ih]

private theorem triple_volume [DecidableEq V] (l : List (Finset V))
    (h : ∀ s ∈ l, s.card = 3) : (joinScopes l).card ≤ 3*l.length ∧
    ((joinScopes l).card = 3*l.length ↔ l.Pairwise Disjoint) := by
  induction l with
  | nil => simp [joinScopes]
  | cons s t ih =>
    obtain ⟨hle,heq⟩ := ih (fun z hz => h z (.tail _ hz))
    have hs := h s (.head ..)
    have hu := Finset.card_union_le s (joinScopes t)
    have hdis : Disjoint s (joinScopes t) ↔ ∀ z ∈ t, Disjoint s z := by
      simp only [Finset.disjoint_left]
      constructor
      · intro h z hz i hi his
        exact h hi ((in_join i t).2 ⟨z,hz,his⟩)
      · intro h i hi hit
        obtain ⟨z,hz,hiz⟩ := (in_join i t).1 hit
        exact h z hz hi hiz
    simp only [joinScopes,List.length_cons,List.pairwise_cons]
    constructor
    · omega
    · constructor
      · intro he
        refine ⟨hdis.mp (Finset.card_union_eq_card_add_card.mp (by omega)),heq.mp (by omega)⟩
      · rintro ⟨hd,hp⟩
        rw [Finset.card_union_of_disjoint (hdis.mpr hd),hs,heq.mpr hp]
        omega

/-- With 3q vertices and all scopes of size three, degree q is possible
    precisely when the scopes contain an exact cover. -/
theorem consensus_iff_exact_triples [Fintype V] {B : Set (Finset V)}
    (paths : ∀ i j, Relation.ReflTransGen (adjacent B) i j) (r : V)
    (heven : Even (Fintype.card V)) (q : ℕ) (hq : Fintype.card V = 3*q)
    (three : ∀ s ∈ B, s.card = 3) :
    consensus V ∈ space (disagreement B) q ↔
      ∃ l : List (Finset V), (∀ s ∈ l, s ∈ B) ∧ l.Pairwise Disjoint ∧
        ∀ i, ∃ s ∈ l, i ∈ s := by
  classical
  rw [consensus_iff_cover paths r heven]
  have size (l : List (Finset V)) (cov : ∀ i, ∃ s ∈ l, i ∈ s) :
      (joinScopes l).card = 3*q := by
    rw [Finset.eq_univ_of_forall (fun i => (in_join i l).2 (cov i))]
    exact hq
  constructor
  · rintro ⟨l,hl,hB,hc⟩
    obtain ⟨hle,he⟩ := triple_volume l (fun s hs => three s (hB s hs))
    have := size l hc
    exact ⟨l,hB,he.mp (by omega),hc⟩
  · rintro ⟨l,hB,hp,hc⟩
    have := (triple_volume l (fun s hs => three s (hB s hs))).2.mpr hp
    have := size l hc
    exact ⟨l,by omega,hB,hc⟩

end CutDegree
