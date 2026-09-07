import Mettapedia.GraphTheory.FourColor.IntegralMaxFlow
import Mathlib.Algebra.BigOperators.Fin

/-!
# Extract simple routes from a positive integer flow

A positive flow reaches the sink through positive-flow arcs, since
otherwise its reachable cut would carry nonpositive outgoing flow.
Subtracting a simple positive route preserves feasibility and decreases
the value by one. Iteration produces any prescribed number of routes up
to the flow value. On arcs with zero reverse capacity, their total usage
is bounded by the original flow. In particular a unit gate cannot be
used by two extracted routes. These are the vertex gates of the contour
linkage construction, not edges of a reduced local carrier.
-/

namespace Mettapedia.GraphTheory.FourColor.IntegralFlow

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

def Network.Allowed (N : Network V) (u v : V) : Prop := 0 < N.capacity u v

namespace Flow

def positive (f : Flow N) (u v : V) : Prop := 0 < f.amount u v

omit [DecidableEq V] in
theorem positive_allowed (f : Flow N) {u v : V} (h : f.positive u v) : N.Allowed u v := by
  have hc := f.bounded u v
  change 0 < f.amount u v at h
  unfold Network.Allowed
  omega

/-- A positive source value supplies a simple positive-flow route. -/
theorem exists_positive_route (f : Flow N) (hf : 0 < f.value) :
    ∃ p : Route f.positive N.source N.sink, p.support.Nodup := by
  classical
  apply Route.exists_simple
  by_contra hn
  let S := Finset.univ.filter (Relation.ReflTransGen f.positive N.source)
  have hmem (u : V) : u ∈ S ↔ Relation.ReflTransGen f.positive N.source u := by simp [S]
  have hs : N.source ∈ S := (hmem _).mpr .refl
  have ht : N.sink ∉ S := fun h => hn ((hmem _).mp h)
  have hcut : (∑ u ∈ S, ∑ v ∈ Sᶜ, f.amount u v) ≤ 0 := by
    apply Finset.sum_nonpos
    intro u hu
    apply Finset.sum_nonpos
    intro v hv
    by_contra h
    have hp : f.positive u v := by change 0 < f.amount u v; omega
    exact Finset.mem_compl.mp hv ((hmem _).mpr (((hmem _).mp hu).tail hp))
  rw [← f.value_eq_cut_flow S hs ht] at hcut
  omega

/-- Remove one route without creating a capacity violation in either direction. -/
def subtract (f : Flow N) (p : Route f.positive N.source N.sink)
    (hp : p.support.Nodup) : Flow N where
  amount u v := f.amount u v - p.delta u v
  bounded u v := by
    by_cases h : f.positive v u
    · have hd := p.delta_le_one hp v u
      have hs := p.delta_skew u v
      have hf := f.skew u v
      have hc : (0 : ℤ) ≤ N.capacity u v := Int.natCast_nonneg _
      change 0 < f.amount v u at h
      omega
    · have hd := p.delta_nonpos_of_not_rel v u h
      have hs := p.delta_skew u v
      have hc := f.bounded u v
      omega
  skew u v := by
    rw [f.skew u v, p.delta_skew u v]
    omega
  conserve u hs ht := by
    rw [Finset.sum_sub_distrib, f.conserve u hs ht, p.sum_delta u]
    simp [hs, ht]

theorem value_subtract (f : Flow N) (p : Route f.positive N.source N.sink)
    (hp : p.support.Nodup) : (f.subtract p hp).value = f.value - 1 := by
  simp [value, subtract, Finset.sum_sub_distrib, Route.sum_delta, N.distinct]

omit [DecidableEq V] in
theorem amount_nonneg_of_reverse_zero (f : Flow N) {u v : V}
    (h : N.capacity v u = 0) : 0 ≤ f.amount u v := by
  have hc := f.bounded v u
  rw [h] at hc
  have hs := f.skew u v
  omega

/-- Total route usage is bounded on every arc with no reverse capacity. -/
theorem exists_routes (f : Flow N) (m : ℕ) (hm : (m : ℤ) ≤ f.value) :
    ∃ paths : Fin m → Route N.Allowed N.source N.sink,
      (∀ i, (paths i).support.Nodup) ∧
      ∀ u v, N.capacity v u = 0 → (∑ i, (paths i).delta u v) ≤ f.amount u v := by
  induction m generalizing f with
  | zero =>
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    intro u v h
    simpa using f.amount_nonneg_of_reverse_zero h
  | succ m ih =>
    have hpos : 0 < f.value := by omega
    obtain ⟨p, hp⟩ := f.exists_positive_route hpos
    let g := f.subtract p hp
    have hg : (m : ℤ) ≤ g.value := by
      dsimp [g]
      rw [value_subtract]
      omega
    obtain ⟨paths, hn, hb⟩ := ih g hg
    let q := p.map (fun _ _ h => f.positive_allowed h)
    refine ⟨Fin.cases q paths, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => hn j) i
      simpa [q] using hp
    · intro u v h
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      have ht := hb u v h
      change (∑ i, (paths i).delta u v) ≤ f.amount u v - p.delta u v at ht
      change q.delta u v + (∑ i, (paths i).delta u v) ≤ f.amount u v
      dsimp [q]
      rw [Route.delta_map]
      omega

end Flow

namespace Route

omit [Fintype V] in
theorem delta_nonneg_of_reverse_zero {a b : V} (p : Route N.Allowed a b) {u v : V}
    (h : N.capacity v u = 0) : 0 ≤ p.delta u v := by
  have hn : ¬ N.Allowed v u := by simp [Network.Allowed, h]
  have hd := p.delta_nonpos_of_not_rel v u hn
  have hs := p.delta_skew u v
  omega

/-- The capacity bound prevents two extracted routes sharing a unit gate. -/
theorem unit_gate_disjoint {m : ℕ} (f : Flow N)
    (paths : Fin m → Route N.Allowed N.source N.sink)
    (hb : ∀ u v, N.capacity v u = 0 → (∑ i, (paths i).delta u v) ≤ f.amount u v)
    {i j : Fin m} (hij : i ≠ j) {u v : V}
    (huv : N.capacity u v = 1) (hvu : N.capacity v u = 0)
    (hi : (paths i).delta u v = 1) (hj : (paths j).delta u v = 1) : False := by
  classical
  have hsub : ({i, j} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun t _ _ => (paths t).delta_nonneg_of_reverse_zero hvu)
  have ht := hb u v hvu
  have hc := f.bounded u v
  rw [huv] at hc
  simp only [Finset.sum_pair hij, hi, hj] at hle
  omega

end Route
end Mettapedia.GraphTheory.FourColor.IntegralFlow
