import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteVelocityLipschitz
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Material trajectories for the constructed local infinite velocity

The real lifted velocity is uniformly bounded and globally Lipschitz in
space on the local time interval. Picard--Lindelof therefore constructs
a trajectory through every real initial point for that entire interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialTrajectories

open scoped BigOperators NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeInfiniteVelocityLipschitz PancakeFourierMaterialPaths
open PancakeIndexedFourierMoments PancakeCurlOutputTail PancakeSobolevSpaceTime
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open Set Metric

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

def liftedVelocity {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (x : X3) : X3 :=
  fun i ↦ (spatialField s t (torusPoint x) i).re

theorem norm_realPart_le (z : VelocityCoefficient) :
    ‖fun i ↦ (z i).re‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)

theorem liftedVelocity_continuousOn {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (x : X3) :
    ContinuousOn (fun t ↦ liftedVelocity s t x) (Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_pi
  intro i
  exact Complex.continuous_re.comp ((continuous_apply i).comp
    ((spatialField_joint_continuous s).comp (continuous_id.prodMk continuous_const)))

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients t) q ≤ g q)

include hg hSum hu

theorem norm_liftedVelocity_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : X3) :
    ‖liftedVelocity s t x‖ ≤ ∑' q, g q := by
  apply (norm_realPart_le _).trans
  apply norm_fullFourierField_le _ g hg hSum
  intro q
  exact (norm_coefficient_le_indexedFirstMoment id _ q).trans (by
    simpa only [indexedFirstMoment_id] using hu t ht q)

theorem lipschitzWith_liftedVelocity (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)) (liftedVelocity s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hgn : 0 ≤ ∑' q, g q := tsum_nonneg hg
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have hreal : liftedVelocity s t x - liftedVelocity s t y =
      fun i ↦ (spatialField s t (torusPoint x) i -
        spatialField s t (torusPoint y) i).re := by
    ext i; simp [liftedVelocity]
  rw [hreal]
  exact (norm_realPart_le _).trans
    (norm_fullFourierField_lift_sub_le _ g hg hSum (hu t ht) x y)

/-- Existence is on the same closed time interval, including one-sided
endpoint derivatives. No trajectory equation is assumed as input. -/
theorem exists_materialTrajectory (hT : 0 ≤ T) (x : X3) :
    ∃ X : ℝ → X3, X 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt X (liftedVelocity s t (X t)) (Icc (0 : ℝ) T) t := by
  let L : ℝ≥0 := ⟨∑' q, g q, tsum_nonneg hg⟩
  let K : ℝ≥0 := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)
  let a : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.2 hT⟩
  have hp : IsPicardLindelof (liftedVelocity s) (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T)
      x a 0 L K := {
    lipschitzOnWith := fun t ht ↦ (lipschitzWith_liftedVelocity s g hg hSum hu t ht).lipschitzOnWith
    continuousOn := fun y _ ↦ liftedVelocity_continuousOn s y
    norm_le := fun t ht y _ ↦ norm_liftedVelocity_le s g hg hSum hu t ht y
    mul_max_le := by simp only [sub_zero, sub_self, max_eq_left hT, NNReal.coe_zero]; exact le_rfl }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_materialTrajectory_interior (hT : 0 < T) (x : X3) :
    ∃ X : ℝ → X3, X 0 = x ∧ ContinuousOn X (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t := by
  obtain ⟨X, hX0, hX⟩ := exists_materialTrajectory s g hg hSum hu hT.le x
  refine ⟨X, hX0, HasDerivWithinAt.continuousOn hX, fun t ht ↦ ?_⟩
  exact (hX t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialTrajectories
