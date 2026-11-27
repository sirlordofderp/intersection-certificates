import AffineShortfall
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Linear invariants of supports with prescribed induced degree parity. -/
namespace ReciprocalHull

open AffineShortfall (Bit)
open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def edge (v w : V) : Bit := if G.Adj v w then 1 else 0

def Model (d : V → Bit) (s : Finset V) : Prop :=
  ∀ v ∈ s, (∑ w ∈ s, edge G v w) = d v

def Invariant (d a : V → Bit) : Prop :=
  ∀ s, Model G d s → ∑ v ∈ s, a v = 0

private theorem alternating_total (E : V → V → Bit) (hs : ∀ v w, E v w = E w v)
    (hz : ∀ v, E v v = 0) (s : Finset V) : ∑ v ∈ s, ∑ w ∈ s, E v w = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, hz, zero_add, Finset.sum_add_distrib, ih, add_zero]
    rw [show (∑ j ∈ s, E j i) = ∑ j ∈ s, E i j from Finset.sum_congr rfl (fun j _ => hs j i)]
    exact CharTwo.add_self_eq_zero _

theorem component_invariant {d a c : V → Bit} (h : ∀ v, a v = c v * d v)
    (hc : ∀ v w, G.Adj v w → c v = c w) : Invariant G d a := by
  intro s hm
  calc
    ∑ v ∈ s, a v = ∑ v ∈ s, ∑ w ∈ s, c v * edge G v w := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [h, ← hm v hv, Finset.mul_sum]
    _ = 0 := by
      apply alternating_total
      · intro v w
        by_cases e : G.Adj v w
        · simp [edge, e, e.symm, hc v w e]
        · have en : ¬G.Adj w v := fun hh => e hh.symm
          simp [edge, e, en]
      · simp [edge]

omit [DecidableEq V] in
theorem singleton_zero {d a : V → Bit} (h : Invariant G d a) (v : V) (hv : d v = 0) :
    a v = 0 := by
  have hm : Model G d {v} := by
    intro w hw
    obtain rfl := Finset.mem_singleton.mp hw
    rw [Finset.sum_singleton]
    simp [edge, hv]
  simpa using h {v} hm

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem adjacent_indices {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (i j : Fin (p.length+1)) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have levels (t : Fin (p.length+1)) : G.dist u (p.getVert t) = t.val := by
    rw [← length_eq_dist_of_subwalk hp (p.isSubwalk_take t), Walk.take_length, Nat.min_eq_left]
    omega
  constructor
  · intro e
    have diff := e.diff_dist_adj (u := u)
    rw [levels, levels] at diff
    have ne : i.val ≠ j.val := fun eq => e.ne (congrArg p.getVert eq)
    omega
  · rintro (eq | eq)
    · rw [← eq]
      exact p.adj_getVert_succ (by omega)
    · rw [← eq]
      exact (p.adj_getVert_succ (by omega)).symm

private theorem index_sum (n t : ℕ) :
    (∑ j : Fin (n+1), (if j.val = t then (1 : Bit) else 0)) =
      if t ≤ n then 1 else 0 := by
  by_cases h : t ≤ n
  · let it : Fin (n+1) := ⟨t, by omega⟩
    have hh (j : Fin (n+1)) : j.val = t ↔ j = it := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
    simp [hh, h]
  · have hh (j : Fin (n+1)) : j.val ≠ t := by omega
    simp [hh, h]

omit [DecidableEq V] in
private theorem path_degree {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (i : Fin (p.length+1)) :
    (∑ j : Fin (p.length+1), edge G (p.getVert i) (p.getVert j)) =
      (if i.val = 0 then 0 else 1) + (if i.val < p.length then 1 else 0) := by
  have point (j : Fin (p.length+1)) :
      edge G (p.getVert i) (p.getVert j) =
        (if i.val ≠ 0 ∧ j.val = i.val-1 then 1 else 0) +
        (if j.val = i.val+1 then 1 else 0) := by
    simp only [edge, adjacent_indices G p hp]
    split_ifs <;> first | rfl | omega
  simp_rw [point]
  rw [Finset.sum_add_distrib, index_sum]
  by_cases h : i.val = 0
  · simp [h, Nat.succ_le_iff]
  · have hh (j : Fin (p.length+1)) : (i.val ≠ 0 ∧ j.val = i.val-1) ↔ j.val = i.val-1 :=
      ⟨And.right, fun e => ⟨h, e⟩⟩
    simp_rw [hh]
    rw [index_sum]
    simp [h, show i.val - 1 ≤ p.length by omega]

/-- Every invariant is constant on marked vertices in each connected component. -/
theorem marked_agree {d a : V → Bit} (H : Invariant G d a)
    {u v : V} (reach : G.Reachable u v) (hu : d u = 1) (hv : d v = 1) : a u = a v := by
  classical
  by_contra hne
  let Bad (n : ℕ) := ∃ u v, G.Reachable u v ∧ d u = 1 ∧ d v = 1 ∧
    a u ≠ a v ∧ G.dist u v = n
  have ex : ∃ n, Bad n := ⟨_, u, v, reach, hu, hv, hne, rfl⟩
  obtain ⟨s, t, hst, hs, ht, hval, hmin⟩ := Nat.find_spec ex
  obtain ⟨p, _, hp⟩ := hst.exists_path_of_dist
  have hlen : 0 < p.length := by
    by_contra! hz
    have eq : p.length = 0 := by omega
    have h := p.getVert_length
    rw [eq, p.getVert_zero] at h
    exact hval (congrArg a h)
  let f (i : Fin (p.length+1)) := p.getVert i
  have level (i : Fin (p.length+1)) : G.dist s (f i) = i.val := by
    rw [← length_eq_dist_of_subwalk hp (p.isSubwalk_take i), Walk.take_length, Nat.min_eq_left]
    omega
  have inj : Function.Injective f := fun i j e => Fin.ext ((level i).symm.trans
    ((congrArg (G.dist s) e).trans (level j)))
  have inside (i : Fin (p.length+1)) (hi : 0 < i.val) (hj : i.val < p.length) :
      d (f i) = 0 := by
    apply (AffineShortfall.bit_eq_zero_or_one _).resolve_right
    intro hd
    by_cases ha : a s = a (f i)
    · have right : G.dist (f i) t ≤ p.length - i.val := by
        simpa [f, Walk.drop_length] using G.dist_le (p.drop i)
      have bad : Bad (G.dist (f i) t) :=
        ⟨_, _, (p.drop i).reachable, hd, ht, fun eq => hval (ha.trans eq), rfl⟩
      have bound := Nat.find_min' ex bad
      omega
    · have bad : Bad i.val := ⟨_, _, (p.take i).reachable, hs, hd, ha, level i⟩
      have bound := Nat.find_min' ex bad
      omega
  let S := Finset.univ.image f
  have hm : Model G d S := by
    rintro _ hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    change (∑ w ∈ Finset.univ.image f, edge G (f i) w) = _
    rw [Finset.sum_image (fun _ _ _ _ e => inj e), path_degree G p hp]
    by_cases h0 : i.val = 0
    · simp [f, h0, hlen, hs]
    by_cases he : i.val = p.length
    · simp [f, he, hlen.ne', ht]
    · have hi : i.val < p.length := by omega
      rw [inside i (by omega) hi]
      simp [h0, hi, CharTwo.add_self_eq_zero]
  have zero := H S hm
  change (∑ w ∈ Finset.univ.image f, a w) = 0 at zero
  rw [Finset.sum_image (fun _ _ _ _ e => inj e)] at zero
  let last : Fin (p.length+1) := Fin.last p.length
  have entry (i : Fin (p.length+1)) : a (f i) =
      (if i = 0 then a s else 0) + (if i = last then a t else 0) := by
    by_cases h0 : i = 0
    · subst i
      have ne : (0 : Fin (p.length+1)) ≠ last := fun e => by
        have := congrArg Fin.val e
        simp [last] at this
        omega
      simp [f, ne]
    by_cases he : i = last
    · subst i
      simp [f, last, h0]
    · have ii : 0 < i.val := by
        exact Nat.pos_of_ne_zero (fun eq => h0 (Fin.ext eq))
      have ij : i.val < p.length := by
        have neq : i.val ≠ p.length := fun eq => he (Fin.ext eq)
        omega
      simp [h0, he, singleton_zero G H _ (inside i ii ij)]
  simp_rw [entry] at zero
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at zero
  rcases AffineShortfall.bit_eq_zero_or_one (a s) with h | h <;>
    rcases AffineShortfall.bit_eq_zero_or_one (a t) with hh | hh <;>
    simp_all

/-- Exact dual description of the affine hull, including mixed labels, isolated
vertices, and disconnected graphs. A component chooses one multiplier. -/
theorem invariant_iff {d a : V → Bit} :
    Invariant G d a ↔ ∃ c : V → Bit, (∀ v, a v = c v * d v) ∧
      ∀ v w, G.Adj v w → c v = c w := by
  classical
  constructor
  · intro H
    let mark (v : V) := ∃ w, G.Reachable v w ∧ d w = 1 ∧ a w = 1
    refine ⟨fun v => if mark v then 1 else 0, ?_, ?_⟩
    · intro v
      rcases AffineShortfall.bit_eq_zero_or_one (d v) with hz | ho
      · simp [hz, singleton_zero G H v hz]
      · by_cases hm : mark v
        · obtain ⟨w, hr, hd, ha⟩ := hm
          have hm : mark v := ⟨w, hr, hd, ha⟩
          simpa [hm, ho] using (marked_agree G H hr ho hd).trans ha
        · have az : a v = 0 := (AffineShortfall.bit_eq_zero_or_one _).resolve_right
            (fun ha => hm ⟨v, Reachable.refl _, ho, ha⟩)
          simp [az, hm]
    · intro v w e
      have same : mark v ↔ mark w := by
        constructor
        · rintro ⟨z, hr, hd, ha⟩
          exact ⟨z, e.symm.reachable.trans hr, hd, ha⟩
        · rintro ⟨z, hr, hd, ha⟩
          exact ⟨z, e.reachable.trans hr, hd, ha⟩
      simp [same]
  · rintro ⟨c, hc, he⟩
    exact component_invariant G hc he

/-- An odd affine probe has a genuine satisfying support exactly when its
weight is outside the component invariants. -/
theorem odd_probe_iff {d a : V → Bit} :
    (∃ s, Model G d s ∧ ∑ v ∈ s, a v = 1) ↔
      ¬ ∃ c : V → Bit, (∀ v, a v = c v * d v) ∧ ∀ v w, G.Adj v w → c v = c w := by
  classical
  rw [← invariant_iff G]
  constructor
  · rintro ⟨s, hs, ha⟩ h
    exact zero_ne_one ((h s hs).symm.trans ha)
  · intro h
    by_contra! hall
    exact h (fun s hs => (AffineShortfall.bit_eq_zero_or_one _).resolve_right (hall s hs))

end ReciprocalHull
