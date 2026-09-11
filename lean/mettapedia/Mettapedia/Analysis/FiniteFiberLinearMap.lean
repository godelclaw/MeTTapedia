import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Linear maps applied to finite fiber sums -/

set_option autoImplicit false

namespace Mettapedia.Analysis

open scoped BigOperators

variable {ι κ R E F : Type*} [Semiring R]
variable [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]

theorem sum_apply_fiberwise (I : Finset ι) (K : Finset κ) (f : ι → κ)
    (v : ι → E) (L : κ → E →ₗ[R] F) [DecidableEq κ]
    (h : ∀ i ∈ I, f i ∈ K) :
    (∑ k ∈ K, L k (∑ i ∈ I with f i = k, v i)) = ∑ i ∈ I, L (f i) (v i) := by
  simp only [map_sum]
  calc
    _ = ∑ k ∈ K, ∑ i ∈ I with f i = k, L (f i) (v i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to h (fun i ↦ L (f i) (v i))

end Mettapedia.Analysis
