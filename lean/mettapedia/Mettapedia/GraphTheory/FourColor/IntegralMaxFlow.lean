import Mettapedia.GraphTheory.FourColor.IntegralFlowPaths
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite integer max-flow/min-cut

An integer skew flow has an attained maximum value: the zero flow is
feasible and the source capacity bounds the integer values above. A
simple residual route would increase the maximum by one, so none exists.
The residual-reachable shore therefore has every outward edge saturated;
its capacity equals the maximum value by conservation and cancellation.

This is the generic integral theorem used by vertex splitting in the
contour separator/linkage construction. No real-flow rounding principle,
assumed optimizer, or executable search oracle is part of the statement.
-/

namespace Mettapedia.GraphTheory.FourColor.IntegralFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Network (V : Type*) where
  capacity : V → V → ℕ
  source : V
  sink : V
  distinct : source ≠ sink

structure Flow (N : Network V) where
  amount : V → V → ℤ
  bounded : ∀ u v, amount u v ≤ N.capacity u v
  skew : ∀ u v, amount u v = -amount v u
  conserve : ∀ u, u ≠ N.source → u ≠ N.sink → ∑ v, amount u v = 0

namespace Flow

variable {N : Network V}

def value (f : Flow N) : ℤ := ∑ v, f.amount N.source v

def zero (N : Network V) : Flow N where
  amount _ _ := 0
  bounded _ _ := by positivity
  skew _ _ := by simp
  conserve _ _ _ := by simp

def residual (f : Flow N) (u v : V) : Prop := f.amount u v < N.capacity u v

/-- Unit augmentation preserves every flow constraint. -/
def augment (f : Flow N) (p : Route f.residual N.source N.sink)
    (hp : p.support.Nodup) : Flow N where
  amount u v := f.amount u v + p.delta u v
  bounded u v := by
    by_cases h : f.residual u v
    · have hle := p.delta_le_one hp u v
      change f.amount u v < (N.capacity u v : ℤ) at h
      omega
    · have hle := p.delta_nonpos_of_not_rel u v h
      have hf := f.bounded u v
      omega
  skew u v := by
    rw [f.skew u v, p.delta_skew u v]
    omega
  conserve u hs ht := by
    rw [Finset.sum_add_distrib, f.conserve u hs ht, p.sum_delta u]
    simp [hs, ht]

theorem value_augment (f : Flow N) (p : Route f.residual N.source N.sink)
    (hp : p.support.Nodup) : (f.augment p hp).value = f.value + 1 := by
  simp [value, augment, Finset.sum_add_distrib, Route.sum_delta, N.distinct]

omit [DecidableEq V] in
/-- There is an actual integer-valued maximizer, not just a supremum. -/
theorem exists_maximum (N : Network V) :
    ∃ f : Flow N, ∀ g : Flow N, g.value ≤ f.value := by
  obtain ⟨z, ⟨f, hf⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ f : Flow N, f.value = z)
    ⟨∑ v, (N.capacity N.source v : ℤ), by
      rintro z ⟨f, rfl⟩
      exact Finset.sum_le_sum fun v _ => f.bounded N.source v⟩
    ⟨(zero N).value, zero N, rfl⟩
  refine ⟨f, fun g => ?_⟩
  rw [hf]
  exact hz g.value ⟨g, rfl⟩

theorem not_reachable_of_maximum (f : Flow N) (hmax : ∀ g : Flow N, g.value ≤ f.value) :
    ¬ Relation.ReflTransGen f.residual N.source N.sink := by
  intro h
  obtain ⟨p, hp⟩ := Route.exists_simple h
  have hle := hmax (f.augment p hp)
  rw [value_augment] at hle
  omega

omit [DecidableEq V] in
/-- The two orientations of internal edges cancel on every vertex set. -/
theorem internal_sum_zero (f : Flow N) (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, f.amount u v = 0 := by
  have h : (∑ u ∈ S, ∑ v ∈ S, f.amount u v) =
      -(∑ u ∈ S, ∑ v ∈ S, f.amount u v) := by
    calc
      _ = ∑ v ∈ S, ∑ u ∈ S, f.amount u v := Finset.sum_comm
      _ = ∑ v ∈ S, ∑ u ∈ S, -f.amount v u := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        exact f.skew u v
      _ = _ := by simp only [Finset.sum_neg_distrib]
  omega

/-- Conservation identifies source value with the entire outgoing cut flow. -/
theorem value_eq_cut_flow (f : Flow N) (S : Finset V)
    (hs : N.source ∈ S) (ht : N.sink ∉ S) :
    f.value = ∑ u ∈ S, ∑ v ∈ Sᶜ, f.amount u v := by
  have hdiv : (∑ u ∈ S, ∑ v, f.amount u v) = f.value := by
    apply Finset.sum_eq_single N.source
    · intro u hu hne
      exact f.conserve u hne (fun h => ht (h ▸ hu))
    · exact fun h => (h hs).elim
  have hsplit (u : V) :
      (∑ v ∈ S, f.amount u v) + (∑ v ∈ Sᶜ, f.amount u v) = ∑ v, f.amount u v :=
    Finset.sum_add_sum_compl S _
  rw [← hdiv]
  simp_rw [← hsplit]
  rw [Finset.sum_add_distrib, f.internal_sum_zero S, zero_add]

def cutCapacity (N : Network V) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (N.capacity u v : ℤ)

theorem capacity_le_cut (N : Network V) (S : Finset V) {u v : V}
    (hu : u ∈ S) (hv : v ∉ S) : (N.capacity u v : ℤ) ≤ cutCapacity N S := by
  calc
    (N.capacity u v : ℤ) ≤ ∑ w ∈ Sᶜ, (N.capacity u w : ℤ) :=
      Finset.single_le_sum (fun w _ => Int.natCast_nonneg _) (Finset.mem_compl.mpr hv)
    _ ≤ ∑ z ∈ S, ∑ w ∈ Sᶜ, (N.capacity z w : ℤ) :=
      Finset.single_le_sum (fun z _ => Finset.sum_nonneg fun w _ => Int.natCast_nonneg _) hu

theorem value_le_cut (f : Flow N) (S : Finset V)
    (hs : N.source ∈ S) (ht : N.sink ∉ S) : f.value ≤ cutCapacity N S := by
  rw [f.value_eq_cut_flow S hs ht]
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => f.bounded u v

/-- Reachability closure produces a saturated cut when the sink is unreachable. -/
theorem exists_saturated_cut (f : Flow N)
    (hnot : ¬ Relation.ReflTransGen f.residual N.source N.sink) :
    ∃ S : Finset V, N.source ∈ S ∧ N.sink ∉ S ∧ f.value = cutCapacity N S := by
  classical
  let S := (Finset.univ : Finset V).filter (Relation.ReflTransGen f.residual N.source)
  have hmem (v : V) : v ∈ S ↔ Relation.ReflTransGen f.residual N.source v := by
    simp [S]
  have hs : N.source ∈ S := (hmem _).mpr .refl
  have ht : N.sink ∉ S := fun h => hnot ((hmem _).mp h)
  refine ⟨S, hs, ht, ?_⟩
  rw [f.value_eq_cut_flow S hs ht]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hnotv : v ∉ S := Finset.mem_compl.mp hv
  have hsat : ¬ f.residual u v := by
    intro h
    exact hnotv ((hmem _).mpr (((hmem _).mp hu).tail h))
  have hcap := f.bounded u v
  change ¬ f.amount u v < (N.capacity u v : ℤ) at hsat
  omega

/-- Integral max-flow/min-cut, with both the maximizer and the cut constructed. -/
theorem exists_max_flow_min_cut (N : Network V) :
    ∃ (f : Flow N) (S : Finset V), N.source ∈ S ∧ N.sink ∉ S ∧
      f.value = cutCapacity N S ∧ (∀ g : Flow N, g.value ≤ f.value) ∧
      ∀ T : Finset V, N.source ∈ T → N.sink ∉ T → cutCapacity N S ≤ cutCapacity N T := by
  obtain ⟨f, hmax⟩ := exists_maximum N
  obtain ⟨S, hs, ht, heq⟩ := f.exists_saturated_cut (f.not_reachable_of_maximum hmax)
  exact ⟨f, S, hs, ht, heq, hmax, fun T hTs hTt => heq ▸ f.value_le_cut T hTs hTt⟩

end Flow
end Mettapedia.GraphTheory.FourColor.IntegralFlow
