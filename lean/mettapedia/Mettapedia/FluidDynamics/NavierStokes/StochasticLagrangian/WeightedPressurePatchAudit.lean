import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedPressurePatch

/-! Regression and axiom audit for weighted pressure patches and gap cutoffs. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedPressurePatchAudit

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeAnisotropyDepletion SpectralGapTiltWeight
open PancakeQuadraticFourierSupport QuadraticFourierWeightApproximation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

example : gapCutoff 1 (3 / 2) = 1 / 2 := by norm_num [gapCutoff]

example : gapCutoff 1 2 = 1 := by norm_num [gapCutoff]

/-- A collision is not erased: its full coarse source cost remains. -/
example (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3)
    (hgap : topGap S = 0) :
    tiltWeight gamma S w = 0 ∧ collisionCost gamma S R w = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  have hle : topGap S ≤ gamma := by rw [hgap]; exact hg.le
  exact ⟨tiltWeight_eq_zero gamma S w hg hle, by
    simp only [collisionCost, gapCutoff_eq_zero gamma _ hg hle, sub_zero, one_mul]⟩

/-- Above the transition the exact inverse-gap weight is recovered. -/
example (gamma : ℝ) (hg : 0 < gamma) (S : SymmetricStrain) (w : R3)
    (hgap : 2 * gamma ≤ topGap S) : tiltWeight gamma S w = ‖w‖ ^ 2 / topGap S ^ 2 := by
  rw [tiltWeight_eq gamma S w hg, gapCutoff_eq_one gamma _ hg hgap, one_mul]

/-- General continuous weights are not required to lie in the unit interval. -/
example (delta : ℝ) (hd : 0 < delta) :
    ∃ c : FourierCoeff (Fin 3), ∀ x : T3, |Complex.normSq (fourierPolynomial c x) - 9| ≤ delta :=
  exists_quadraticWeight_approximation (ContinuousMap.const T3 9) (fun _ ↦ by norm_num) delta hd

/-- Vanishing weight permits arbitrary, even nonmeasurable, line choices. -/
example {X : Type*} [TopologicalSpace X] (R : X → R3 →L[ℝ] R3) (hR : Continuous R)
    (e : X → R3) (he : ∀ x, ‖e x‖ = 1) :
    Continuous (fun x ↦ (0 : ℝ) * ‖lineRemainder (e x) (R x (e x))‖ ^ 2) := by
  apply WeightedProjectorTilt.continuous_weighted_transverse_norm_sq _ continuous_const
    (fun _ ↦ le_rfl) R hR e he
  simpa only [Real.sqrt_zero, _root_.zero_smul ℝ] using
    (continuous_const : Continuous (fun _ : X ↦ (0 : R3 →L[ℝ] R3)))

end Mettapedia.FluidDynamics.NavierStokes.WeightedPressurePatchAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedLineFreezing.sq_mul_lineDistanceSq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedLineFreezing.mul_lineDistanceSq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedLineFreezing.exists_partition_of_continuous_weighted_projector
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedProjectorTilt.norm_transverse_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedProjectorTilt.continuous_weighted_transverse_norm_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedProjectorTilt.weighted_transverse_le_approximation
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuadraticFourierWeightApproximation.abs_normSq_sub_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuadraticFourierWeightApproximation.exists_quadraticWeight_approximation
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuadraticFourierWeightApproximation.exists_finite_quadraticWeight_approximation
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedFourierPressurePatch.exists_weighted_patch_energy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedFourierPressurePatch.exists_weighted_pressure_patches
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.gapCutoff_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.gapCutoff_le_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.gapCutoff_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.gapCutoff_eq_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.continuous_gapCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.tiltWeight_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.tiltWeight_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.tiltWeight_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.continuous_tiltWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.continuous_weighted_projector
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.continuous_weighted_tilt_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.collisionCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.collisionCost_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.excess_le_weighted_tilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralGapTiltWeight.excess_le_capped_weighted_tilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch.continuous_localTiltWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch.exists_local_weighted_pressure_patches
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch.sourceExcess_le_weighted_jointTilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalWeightedPressurePatch.sourceExcess_le_capped_weighted_jointTilt_add_collision
