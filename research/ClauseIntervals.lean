import PEqualNP.Defs.Search
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic

namespace ClauseIntervals

open PEqualNP.Search

/-- A gap in the set of falsified clauses at three selected positions. -/
def Gap (a b c : Clause) (s : Assignment) : Prop :=
  a.eval s = false ∧ b.eval s = true ∧ c.eval s = false

/-- Fix the endpoint literals to false. Conflicting demands may be resolved arbitrarily:
    such endpoints can never witness a gap. -/
def complete (ends : Clause) (d : Bool) : Assignment := fun v =>
  if (v, true) ∈ ends then false else if (v, false) ∈ ends then true else d

private theorem false_iff (s : Assignment) (c : Clause) :
    c.eval s = false ↔ ∀ l ∈ c, s l.1 ≠ l.2 := by
  simp [Clause.eval, Literal.eval, List.any_eq_false]

private theorem true_iff (s : Assignment) (c : Clause) :
    c.eval s = true ↔ ∃ l ∈ c, s l.1 = l.2 := by
  simp [Clause.eval, Literal.eval]

private theorem append_false (s : Assignment) (a c : Clause) :
    (a ++ c).eval s = false ↔ a.eval s = false ∧ c.eval s = false := by
  simp only [Clause.eval, List.any_append, Bool.or_eq_false_iff]

private theorem agrees (e : Clause) (s : Assignment) (h : e.eval s = false)
    (d : Bool) (l : Literal) (hl : l ∈ e) : complete e d l.1 = s l.1 := by
  rcases l with ⟨v,p⟩
  have hf := (false_iff s e).mp h
  by_cases hp : (v,true) ∈ e
  · have hs := hf (v,true) hp
    cases hv : s v <;> simp_all [complete]
  · cases p <;> simp_all [complete]

private theorem chooseDefault (e : Clause) (s : Assignment) (h : e.eval s = false)
    (v : ℕ) : complete e (s v) v = s v := by
  by_cases hp : (v,true) ∈ e
  · exact agrees e s h (s v) (v,true) hp
  by_cases hn : (v,false) ∈ e
  · exact agrees e s h (s v) (v,false) hn
  simp [complete, hp, hn]

theorem gap_iff_two_completions (a b c : Clause) :
    (∃ s, Gap a b c s) ↔ ∃ d : Bool, Gap a b c (complete (a ++ c) d) := by
  constructor
  · rintro ⟨s, ha, hb, hc⟩
    have he : (a ++ c).eval s = false := by
      simpa [Clause.eval, List.any_append, Bool.or_eq_false_iff] using And.intro ha hc
    obtain ⟨l, hl, ht⟩ := (true_iff s b).1 hb
    let d := s l.1
    refine ⟨d, (false_iff _ a).2 ?_, (true_iff _ b).2 ?_, (false_iff _ c).2 ?_⟩
    · intro x hx
      rw [agrees _ s he d x (List.mem_append_left _ hx)]
      exact (false_iff s a).1 ha x hx
    · exact ⟨l, hl, (chooseDefault _ s he _).trans ht⟩
    · intro x hx
      rw [agrees _ s he d x (List.mem_append_right _ hx)]
      exact (false_iff s c).1 hc x hx
  · rintro ⟨d, hd⟩
    exact ⟨_, hd⟩

/-- The indices describe at most 2m² assignments when there are m clauses. -/
def sample (F : CNF) (i : Fin F.length × Fin F.length × Bool) : Assignment :=
  complete (F[i.1] ++ F[i.2.1]) i.2.2

def Represents {ι : Type} (F : CNF) (rows : ι → Assignment) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, (∃ s, Gap a b c s) → ∃ i, Gap a b c (rows i)

theorem sample_represents (F : CNF) : Represents F (sample F) := by
  intro a ha b _ c hc h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨d, hd⟩ := (gap_iff_two_completions _ _ _).mp h
  exact ⟨(⟨i,hi⟩, ⟨j,hj⟩, d), hd⟩

/-- A bank of q clauses, one for each possible one-hot word.
    The two banks use disjoint variable positions and leave position zero for the guard. -/
def slot (bank : Bool) (j : ℕ) : ℕ := 2*j + (if bank then 2 else 1)

def codeClause {q : ℕ} (bank : Bool) (i : Fin q) : Clause :=
  List.ofFn fun j : Fin q => (slot bank j.val, decide (j ≠ i))

private theorem code_false {q : ℕ} (bank : Bool) (i : Fin q) (s : Assignment) :
    (codeClause bank i).eval s = false ↔
      ∀ j : Fin q, s (slot bank j.val) = decide (j = i) := by
  rw [false_iff]
  constructor
  · intro h j
    have hv := h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    change s (slot bank j.val) ≠ decide (j ≠ i) at hv
    by_cases hji : j = i <;> simp_all
  · intro h l hl
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    change s (slot bank j.val) ≠ decide (j ≠ i)
    rw [h]
    by_cases hji : j = i <;> simp [hji]

private theorem code_unique {q : ℕ} {bank : Bool} {i j : Fin q} {s : Assignment}
    (hi : (codeClause bank i).eval s = false)
    (hj : (codeClause bank j).eval s = false) : i = j := by
  have h₁ := (code_false bank i s).mp hi i
  have h₂ := (code_false bank j s).mp hj i
  simpa using h₂.symm.trans h₁

def guardClause : Clause := [(0,true)]

def exampleCNF (q : ℕ) : CNF :=
  guardClause :: (List.ofFn (@codeClause q false) ++ List.ofFn (@codeClause q true))

theorem example_length (q : ℕ) : (exampleCNF q).length = 2*q+1 := by
  simp [exampleCNF]; omega

private theorem pair_gap {q : ℕ} (i j : Fin q) :
    ∃ s, Gap (codeClause false i) guardClause (codeClause true j) s := by
  let s : Assignment := fun v => decide (v = 0 ∨ v = slot false i.val ∨ v = slot true j.val)
  refine ⟨s, (code_false _ _ _).2 ?_, ?_, (code_false _ _ _).2 ?_⟩
  · intro t
    have hn : 2*t.val+1 ≠ 2*j.val+2 := by omega
    have hz : 2*t.val+1 ≠ 0 := by omega
    have he : (2*t.val+1 = 2*i.val+1) ↔ t = i := by rw [Fin.ext_iff]; omega
    simp only [s, slot, Bool.false_eq_true, ite_false, ite_true, hn, hz, he]
    simp
  · simp [guardClause, Clause.eval, Literal.eval, s]
  · intro t
    have hn : 2*t.val+2 ≠ 2*i.val+1 := by omega
    have hz : 2*t.val+2 ≠ 0 := by omega
    have he : (2*t.val+2 = 2*j.val+2) ↔ t = j := by rw [Fin.ext_iff]; omega
    simp only [s, slot, Bool.false_eq_true, ite_false, ite_true, hn, hz, he]
    simp

/-- A universal pool which preserves all gap witnesses for this formula needs q² rows,
    even if the entries are chosen by an arbitrary method. -/
theorem quadratic_lower_bound {ι : Type} [Fintype ι] (q : ℕ) (rows : ι → Assignment)
    (h : Represents (exampleCNF q) rows) : q*q ≤ Fintype.card ι := by
  classical
  have hw (p : Fin q × Fin q) :
      ∃ u, Gap (codeClause false p.1) guardClause (codeClause true p.2) (rows u) := by
    apply h
    · simp [exampleCNF, List.mem_ofFn]
    · simp [exampleCNF]
    · simp [exampleCNF, List.mem_ofFn]
    · exact pair_gap _ _
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro p t heq
    have ht := hf t
    rw [← heq] at ht
    exact Prod.ext (code_unique (hf p).1 ht.1) (code_unique (hf p).2.2 ht.2.2)
  simpa using Fintype.card_le_of_injective f hinj

end ClauseIntervals

namespace ClauseIntervals
open PEqualNP.Search

def TwoGap (a b c d e : Clause) (s : Assignment) : Prop :=
  a.eval s = false ∧ b.eval s = true ∧ c.eval s = false ∧ d.eval s = true ∧ e.eval s = false

def RepresentsTwo {ι : Type} (F : CNF) (rows : ι → Assignment) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F, ∀ e ∈ F,
    (∃ s, TwoGap a b c d e s) → ∃ u, TwoGap a b c d e (rows u)

/-- A literal guaranteed true at either guard is handled by the same clause semantics as
    all the bits. When the three endpoints are false, both guards are forced false. -/
private def bankClause {q : ℕ} (off : ℕ) (i : Fin q) (gs : Clause) : Clause :=
  (List.ofFn fun j : Fin q => (off+j.val, decide (j ≠ i))) ++ gs

private theorem bank_false {q : ℕ} (off : ℕ) (i : Fin q) (gs : Clause) (s : Assignment) :
    (bankClause off i gs).eval s = false ↔
    (∀ j : Fin q, s (off+j.val) = decide (j = i)) ∧ gs.eval s = false := by
  simp only [bankClause, Clause.eval, List.any_append, Bool.or_eq_false_iff]
  apply and_congr_left
  intro _
  change Clause.eval s (List.ofFn _) = false ↔ _
  rw [false_iff]
  constructor
  · intro h j
    have hv := h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    change s (off+j.val) ≠ decide (j ≠ i) at hv
    by_cases hji : j = i <;> simp_all
  · intro h l hl
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    change s (off+j.val) ≠ decide (j ≠ i)
    rw [h]
    by_cases hji : j = i <;> simp [hji]

private theorem bank_unique {q off : ℕ} {i j : Fin q} {gs : Clause} {s : Assignment}
    (hi : (bankClause off i gs).eval s = false)
    (hj : (bankClause off j gs).eval s = false) : i = j := by
  have h₁ := ((bank_false ..).mp hi).1 i
  have h₂ := ((bank_false ..).mp hj).1 i
  simpa using h₂.symm.trans h₁

private def rowA {q : ℕ} (i : Fin q) := bankClause 2 i [(0,true)]
private def rowB {q : ℕ} (i : Fin q) := bankClause (2+q) i [(1,true)]
private def rowC {q : ℕ} (i : Fin q) := bankClause (2+2*q) i []
private def probe (q v : ℕ) (b : Bool) : Clause :=
  [(2+3*q+v,b), (if b then 0 else 1,true)]

def twoExample (q t : ℕ) : CNF :=
  List.ofFn (@rowA q) ++ List.ofFn (@rowB q) ++ List.ofFn (@rowC q) ++
  (List.ofFn fun x : Fin t => probe q x.val true) ++
  (List.ofFn fun x : Fin t => probe q x.val false)

theorem twoExample_length (q t : ℕ) : (twoExample q t).length = 3*q + 2*t := by
  simp [twoExample]; omega

private def FiberOK {q : ℕ} (p : Fin q × Fin q × Fin q) (s : Assignment) : Prop :=
  (rowA p.1).eval s = false ∧ (rowB p.2.1).eval s = false ∧ (rowC p.2.2).eval s = false

private theorem fiber_unique {q : ℕ} {p t : Fin q × Fin q × Fin q} {s : Assignment}
    (h : FiberOK p s) (g : FiberOK t s) : p = t := by
  exact Prod.ext (bank_unique h.1 g.1) (Prod.ext (bank_unique h.2.1 g.2.1)
    (bank_unique h.2.2 g.2.2))

private theorem fiber_pair {q t : ℕ} (p : Fin q × Fin q × Fin q) (x y : Fin t) (hxy : x ≠ y) :
    ∃ s, TwoGap (rowA p.1) (probe q x.val true) (rowB p.2.1)
        (probe q y.val false) (rowC p.2.2) s := by
  let s : Assignment := fun v => decide (v = 2+p.1.val ∨ v = 2+q+p.2.1.val ∨
    v = 2+2*q+p.2.2.val ∨ v = 2+3*q+x.val)
  have ha := p.1.isLt
  have hb := p.2.1.isLt
  have hc := p.2.2.isLt
  have hx : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have atBit (v : ℕ) (P : Prop) [Decidable P]
      (h : (v = 2+p.1.val ∨ v = 2+q+p.2.1.val ∨ v = 2+2*q+p.2.2.val ∨ v = 2+3*q+x.val) ↔ P) :
      s v = decide P := by simp only [s, h]
  have s0 : s 0 = false := atBit 0 False (by simp only [iff_false, not_or]; exact ⟨by omega, by omega, by omega, by omega⟩)
  have s1 : s 1 = false := atBit 1 False (by simp only [iff_false, not_or]; exact ⟨by omega, by omega, by omega, by omega⟩)
  have sx : s (2+3*q+x.val) = true := atBit (2+3*q+x.val) True (by simp)
  have sy : s (2+3*q+y.val) = false := atBit (2+3*q+y.val) False (by simp only [iff_false, not_or]; exact ⟨by omega, by omega, by omega, by omega⟩)
  refine ⟨s, (bank_false ..).2 ⟨?_, ?_⟩, ?_, (bank_false ..).2 ⟨?_, ?_⟩, ?_,
    (bank_false ..).2 ⟨?_, ?_⟩⟩
  · intro j; apply atBit; rw [Fin.ext_iff]; have := j.isLt; omega
  · simp [Clause.eval, Literal.eval, s0]
  · simp [probe, Clause.eval, Literal.eval, sx]
  · intro j; apply atBit; rw [Fin.ext_iff]; have := j.isLt; omega
  · simp [Clause.eval, Literal.eval, s1]
  · simp [probe, Clause.eval, Literal.eval, sy]
  · intro j; apply atBit; rw [Fin.ext_iff]; have := j.isLt; omega
  · rfl

/-- With three decoder banks and 2^b probe bits, every representative pool must
    distinguish the probe coordinates independently in each of q³ disjoint fibers. -/
theorem cubic_log_lower_bound {ι : Type} [Fintype ι] (q b : ℕ) (rows : ι → Assignment)
    (h : RepresentsTwo (twoExample q (2^b)) rows) : q^3 * b ≤ Fintype.card ι := by
  classical
  let K := Fin q × Fin q × Fin q
  let fiber (p : K) := {i : ι // FiberOK p (rows i)}
  have bound (p : K) : b ≤ Fintype.card (fiber p) := by
    let col (x : Fin (2^b)) (u : fiber p) := rows u.val (2+3*q+x.val)
    have inj : Function.Injective col := by
      intro x y eqc
      by_contra ne
      obtain ⟨u, hu⟩ := h _ (by simp [twoExample, List.mem_ofFn])
        _ (by simp [twoExample, List.mem_ofFn])
        _ (by simp [twoExample, List.mem_ofFn])
        _ (by simp [twoExample, List.mem_ofFn])
        _ (by simp [twoExample, List.mem_ofFn]) (fiber_pair p x y ne)
      obtain ⟨ha, hx, hb, hy, hc⟩ := hu
      have s0 := ((bank_false ..).mp ha).2
      have s1 := ((bank_false ..).mp hb).2
      have hh := congrFun eqc (⟨u,ha,hb,hc⟩ : fiber p)
      change rows u (2+3*q+x.val) = rows u (2+3*q+y.val) at hh
      simp [Clause.eval, Literal.eval] at s0 s1
      simp [probe, Clause.eval, Literal.eval, s0, s1] at hx hy
      simp_all
    have hc := Fintype.card_le_of_injective col inj
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  let forget (z : (p : K) × fiber p) : ι := z.2.val
  have hi : Function.Injective forget := by
    rintro ⟨p,u,hu⟩ ⟨t,v,hv⟩ huv
    change u = v at huv
    subst v
    have hp := fiber_unique hu hv
    subst t
    rfl
  have hc := Fintype.card_le_of_injective forget hi
  rw [Fintype.card_sigma] at hc
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset K)) (fun p _ => bound p)
  calc
    q^3*b = ∑ _p : K, b := by simp [K, pow_succ, Nat.mul_assoc]
    _ ≤ _ := hsum
    _ ≤ _ := hc

/-- Two constant rows and the columns of a binary address and their complements. -/
private def stripe {b : ℕ} (enc : ℕ → Fin b → Bool)
    (r : Option (Fin b) × Bool) (v : ℕ) : Bool :=
  match r.1 with
  | none => r.2
  | some j => Bool.xor (enc v j) r.2

private theorem cover_pair {β : Type} [Fintype β] (var : β → ℕ) (b : ℕ)
    (hc : Fintype.card β ≤ 2^b) :
    ∃ bg : Option (Fin b) × Bool → Assignment,
      ∀ (i j : β) (s : Assignment), ∃ r,
        bg r (var i) = s (var i) ∧ bg r (var j) = s (var j) := by
  classical
  obtain ⟨emb⟩ : Nonempty (β ↪ (Fin b → Bool)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  let enc (v : ℕ) : Fin b → Bool :=
    if h : ∃ i, var i = v then emb h.choose else fun _ => false
  refine ⟨stripe enc, ?_⟩
  intro i j s
  by_cases he : s (var i) = s (var j)
  · exact ⟨(none,s (var i)),rfl,he⟩
  have hi : ∃ x, var x = var i := ⟨i,rfl⟩
  have hj : ∃ x, var x = var j := ⟨j,rfl⟩
  have hs : enc (var i) ≠ enc (var j) := by
    intro h
    simp only [enc, dite_eq_left hi, dite_eq_left hj] at h
    exact he (congrArg s (hi.choose_spec.symm.trans
      ((congrArg var (emb.injective h)).trans hj.choose_spec)))
  obtain ⟨u, hu⟩ : ∃ u, enc (var i) u ≠ enc (var j) u := by
    by_contra! h
    exact hs (funext h)
  refine ⟨(some u,Bool.xor (enc (var i) u) (s (var i))), ?_⟩
  simp only [stripe]
  cases ei : enc (var i) u <;> cases ej : enc (var j) u <;>
    cases si : s (var i) <;> cases sj : s (var j) <;> simp_all

private def Witness (e a c : Clause) (w : Assignment × Literal × Literal) : Prop :=
  e.eval w.1 = false ∧ w.2.1 ∈ a ∧ w.1 w.2.1.1 = w.2.1.2 ∧
    w.2.2 ∈ c ∧ w.1 w.2.2.1 = w.2.2.2

private theorem with_endpoints (F : CNF) (e : Clause) (b : ℕ) (hb : 2*F.length^2 ≤ 2^b) :
    ∃ pool : Option (Fin b) × Bool → Assignment,
      ∀ (i j : Fin F.length), (∃ w, Witness e F[i] F[j] w) →
        ∃ r, e.eval (pool r) = false ∧ F[i].eval (pool r) = true ∧ F[j].eval (pool r) = true := by
  classical
  let w (i j : Fin F.length) : Assignment × Literal × Literal :=
    if h : ∃ w, Witness e F[i] F[j] w then h.choose else (fun _ => false, (0,false), (0,false))
  let v (p : Fin F.length × Fin F.length × Bool) :=
    if p.2.2 then (w p.1 p.2.1).2.1.1 else (w p.1 p.2.1).2.2.1
  obtain ⟨bg, hbg⟩ := cover_pair v b (by simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hb)
  let pool (r : Option (Fin b) × Bool) : Assignment := fun x => complete e (bg r x) x
  refine ⟨pool, ?_⟩
  intro i j h
  have hw : Witness e F[i] F[j] (w i j) := by simpa only [w, dite_eq_left h] using h.choose_spec
  obtain ⟨he, hli, hti, hlj, htj⟩ := hw
  obtain ⟨r, h₁, h₂⟩ := hbg (i,j,true) (i,j,false) (w i j).1
  change bg r (w i j).2.1.1 = (w i j).1 (w i j).2.1.1 at h₁
  change bg r (w i j).2.2.1 = (w i j).1 (w i j).2.2.1 at h₂
  refine ⟨r,(false_iff ..).2 ?_, (true_iff ..).2 ⟨_,hli,?_⟩, (true_iff ..).2 ⟨_,hlj,?_⟩⟩
  · intro l hl
    change complete e _ l.1 ≠ l.2
    rw [agrees _ _ he _ l hl]
    exact (false_iff ..).1 he l hl
  · change complete e _ _ = _
    rw [h₁, chooseDefault _ _ he]
    exact hti
  · change complete e _ _ = _
    rw [h₂, chooseDefault _ _ he]
    exact htj

/-- Every CNF with m clauses has a pool of at most m³(2b+2) assignments preserving
    every false/true/false/true/false pattern, provided 2m² ≤ 2^b. -/
theorem cubic_log_upper_bound (F : CNF) (b : ℕ) (hb : 2*F.length^2 ≤ 2^b) :
    ∃ rows : Fin (F.length^3*(2*b+2)) → Assignment, RepresentsTwo F rows := by
  classical
  let K := Fin F.length × Fin F.length × Fin F.length
  let ends (p : K) := F[p.1] ++ F[p.2.1] ++ F[p.2.2]
  choose pool hp using (fun p : K => with_endpoints F (ends p) b hb)
  let J := K × (Option (Fin b) × Bool)
  have card : Fintype.card J = F.length^3*(2*b+2) := by
    simp [J,K,pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  let eqv := Fintype.equivFinOfCardEq card
  refine ⟨fun z => pool (eqv.symm z).1 (eqv.symm z).2, ?_⟩
  intro a ha s hs c hc t ht d hd hh
  obtain ⟨ia,indexa,rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib,hb',rfl⟩ := List.mem_iff_getElem.mp hs
  obtain ⟨ic,indexc,rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨it,indext,rfl⟩ := List.mem_iff_getElem.mp ht
  obtain ⟨id,indexd,rfl⟩ := List.mem_iff_getElem.mp hd
  let p : K := (⟨ia,indexa⟩,⟨ic,indexc⟩,⟨id,indexd⟩)
  obtain ⟨s, fa, tb, fc, tt, fd⟩ := hh
  have fe : (ends p).eval s = false := by
    exact (append_false ..).2 ⟨(append_false ..).2 ⟨fa,fc⟩,fd⟩
  obtain ⟨x,hx,ex⟩ := (true_iff ..).1 tb
  obtain ⟨y,hy,ey⟩ := (true_iff ..).1 tt
  obtain ⟨r,fr,tr,sr⟩ := hp p ⟨ib,hb'⟩ ⟨it,indext⟩ ⟨(s,x,y),fe,hx,ex,hy,ey⟩
  refine ⟨eqv (p,r), ?_⟩
  simp only [Equiv.symm_apply_apply]
  have parts := (append_false ..).1 fr
  have firstParts := (append_false ..).1 parts.1
  exact ⟨firstParts.1,tr,firstParts.2,sr,parts.2⟩

/-- An ordered subsequence has three separate false runs exactly when it has
    a false/true/false/true/false subsequence at five strictly increasing positions. -/
def NoThreeRuns (G : CNF) (s : Assignment) : Prop :=
  ∀ i j k l t : Fin G.length, i < j → j < k → k < l → l < t →
    ¬ TwoGap G[i] G[j] G[k] G[l] G[t] s

theorem all_orders_and_subformulas {ι : Type} {F : CNF} {rows : ι → Assignment}
    (h : RepresentsTwo F rows) (G : CNF) (sub : ∀ c ∈ G, c ∈ F) :
    (∀ s, NoThreeRuns G s) ↔ ∀ u, NoThreeRuns G (rows u) := by
  constructor
  · intro hh u; exact hh _
  · intro hh s i j k l t hij hjk hkl hlt bad
    have mem (z : Fin G.length) : G[z] ∈ F := sub _ (List.getElem_mem ..)
    obtain ⟨u, hu⟩ := h _ (mem i) _ (mem j) _ (mem k) _ (mem l) _ (mem t) ⟨s,bad⟩
    exact hh u i j k l t hij hjk hkl hlt hu

/-- Count the last position of each maximal false run, with a true sentinel. -/
def runs : List Bool → ℕ
  | [] => 0
  | a :: t => (if !a && t.headD true then 1 else 0) + runs t

private theorem runs_zero (t : List Bool) : runs t = 0 ↔ t.all id = true := by
  induction t with
  | nil => simp [runs]
  | cons a t ih =>
    cases a
    · by_cases h : runs t = 0
      · have ht := ih.mp h
        have hd : t.head?.getD true = true := by cases t <;> simp_all
        simp [runs, h, hd]
      · simp [runs, h]
    · simpa [runs] using ih

def runNumber (F : CNF) (s : Assignment) : ℕ := runs (F.map (Clause.eval s))

private theorem run_zero_iff (F : CNF) (s : Assignment) :
    runNumber F s = 0 ↔ F.eval s = true := by
  simpa [runNumber, CNF.eval, List.all_map] using runs_zero (F.map (Clause.eval s))

/-- Summing over any indexed finite assignment domain allows ordinary counting on the
    full Boolean cube or on a restriction. The third factorial moment certifies the cap. -/
def moment {ι : Type} [Fintype ι] (F : CNF) (rows : ι → Assignment) (r : ℕ) : ℕ :=
  ∑ i, (runNumber F (rows i)).choose r

theorem certified_model_count {ι : Type} [Fintype ι] (F : CNF) (rows : ι → Assignment)
    (h : moment F rows 3 = 0) :
    (∑ i, if F.eval (rows i) = true then (1 : ℤ) else 0) =
      (Fintype.card ι : ℤ) - moment F rows 1 + moment F rows 2 := by
  classical
  have hm (i : ι) : (runNumber F (rows i)).choose 3 = 0 :=
    (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ _)
  have point (i : ι) :
      (if F.eval (rows i) = true then (1 : ℤ) else 0) =
      1 - ((runNumber F (rows i)).choose 1 : ℤ) + ((runNumber F (rows i)).choose 2 : ℤ) := by
    simp only [← run_zero_iff]
    have lt : runNumber F (rows i) < 3 := Nat.choose_eq_zero_iff.mp (hm i)
    rcases (show runNumber F (rows i) = 0 ∨ runNumber F (rows i) = 1 ∨
      runNumber F (rows i) = 2 by omega) with h0 | h1 | h2
    · rw [h0]; decide
    · rw [h1]; decide
    · rw [h2]; decide
  simp_rw [point]
  simp [moment, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end ClauseIntervals
