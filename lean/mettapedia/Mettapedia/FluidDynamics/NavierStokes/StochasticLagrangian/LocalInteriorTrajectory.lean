import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialTrajectories

/-!
# Material trajectories through prescribed space-time points

The uniformly bounded, spatially Lipschitz local velocity constructs a
trajectory through a prescribed point at any time in its existence interval.
This does not require a separately constructed inverse flow map.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalInteriorTrajectory

open scoped Topology NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories

local notation "X3" => Fin 3 → ℝ

theorem exists_materialTrajectory_through {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : X3) :
    ∃ X : ℝ → X3, X t = x ∧ ContinuousOn X (Set.Icc (0 : ℝ) T) ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ := by
  let L : ℝ≥0 := ⟨∑' q, g q, tsum_nonneg hg⟩
  let K : ℝ≥0 := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)
  let a : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.2 (ht.1.trans ht.2)⟩
  have hp : IsPicardLindelof (liftedVelocity s) (⟨t, ht⟩ : Set.Icc (0 : ℝ) T)
      x a 0 L K := {
    lipschitzOnWith := fun τ hτ ↦ (lipschitzWith_liftedVelocity s g hg hSum hu τ hτ).lipschitzOnWith
    continuousOn := fun y _ ↦ liftedVelocity_continuousOn s y
    norm_le := fun τ hτ y _ ↦ norm_liftedVelocity_le s g hg hSum hu τ hτ y
    mul_max_le := by
      change (L : ℝ) * max (T - t) (t - 0) ≤ (L : ℝ) * T - 0
      rw [sub_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht.1]) ht.2) L.2 }
  obtain ⟨X, hXt, hX⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨X, hXt, HasDerivWithinAt.continuousOn hX, fun τ hτ ↦ ?_⟩
  exact (hX τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)

end Mettapedia.FluidDynamics.NavierStokes.LocalInteriorTrajectory
