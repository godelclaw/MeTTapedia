import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialStrain

/-!
# A unique, spatially Lipschitz material flow on the local interval

Uniform spatial bounds construct trajectories from all initial points.
Gronwall identifies any two trajectories with the same initial value and
bounds dependence on initial position.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialFlow

open scoped NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeCurlOutputTail
open Set Metric

local notation "X3" => Fin 3 → ℝ

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem materialTrajectory_dist_le (X Y : ℝ → X3)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt X (liftedVelocity s t (X t)) (Icc (0 : ℝ) T) t)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (liftedVelocity s t (Y t)) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    dist (X t) (Y t) ≤ dist (X 0) (Y 0) *
      Real.exp ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t) := by
  have h := dist_le_of_trajectories_ODE_of_mem
    (s := fun _ ↦ (univ : Set X3))
    (fun τ hτ ↦ (lipschitzWith_liftedVelocity s g hg hSum hu τ ⟨hτ.1, hτ.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hX)
    (fun τ hτ ↦ (hX τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun _ _ ↦ mem_univ _) (HasDerivWithinAt.continuousOn hY)
    (fun τ hτ ↦ (hY τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun _ _ ↦ mem_univ _) (le_refl (dist (X 0) (Y 0))) t ht
  simpa only [sub_zero] using h

theorem materialTrajectory_unique (X Y : ℝ → X3)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt X (liftedVelocity s t (X t)) (Icc (0 : ℝ) T) t)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (liftedVelocity s t (Y t)) (Icc (0 : ℝ) T) t)
    (h0 : X 0 = Y 0) : EqOn X Y (Icc (0 : ℝ) T) := by
  intro t ht
  have h := materialTrajectory_dist_le s g hg hSum hu X Y hX hY t ht
  simpa only [h0, dist_self, zero_mul, dist_le_zero] using h

theorem exists_materialFlow (hT : 0 ≤ T) :
    ∃ Φ : X3 → ℝ → X3,
      (∀ x, Φ x 0 = x) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        HasDerivWithinAt (Φ x) (liftedVelocity s t (Φ x t)) (Icc (0 : ℝ) T) t) ∧
      ∃ L : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (fun x ↦ Φ x t) := by
  choose Φ h0 hΦ using exists_materialTrajectory s g hg hSum hu hT
  let K : ℝ≥0 := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)
  refine ⟨Φ, h0, hΦ, ⟨Real.exp ((K : ℝ) * T), (Real.exp_pos _).le⟩, fun t ht ↦ ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := materialTrajectory_dist_le s g hg hSum hu (Φ x) (Φ y) (hΦ x) (hΦ y) t ht
  simp only [h0] at h
  calc
    _ ≤ dist x y * Real.exp ((K : ℝ) * t) := h
    _ ≤ dist x y * Real.exp ((K : ℝ) * T) := by gcongr; exact ht.2
    _ = _ := mul_comm _ _

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialFlow
