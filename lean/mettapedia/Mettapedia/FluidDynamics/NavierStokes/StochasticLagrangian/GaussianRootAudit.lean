import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootEnergy

/-! Regressions for the fourth-power gate, its cost, and zero vorticity. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootAudit

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open SpectralGapTiltWeight GaussianRootVorticity
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail LocalLowDiffusionBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

example (S : SymmetricStrain) (hS : topGap S = 4) : rootGapFactor 1 S = 1 / 2 := by
  have hs : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num [rootGapFactor, hS, gapCutoff, hs]

/-- Half a gap gate leaves fifteen sixteenths of the coarse collision cost. -/
example (S : SymmetricStrain) (hS : topGap S = 3 / 2) (R : R3 →L[ℝ] R3) (w : R3) :
    QuarticGapTiltWeight.collisionCost 1 S R w = (15 / 16 : ℝ) * (2 * ‖R‖ * ‖w‖ ^ 2) ∧
    SquaredGapTiltWeight.collisionCost 1 S R w = (3 / 4 : ℝ) * (2 * ‖R‖ * ‖w‖ ^ 2) := by
  norm_num [QuarticGapTiltWeight.collisionCost, SquaredGapTiltWeight.collisionCost, gapCutoff, hS]

example (S : SymmetricStrain) (hS : topGap S = 1) (w : R3) :
    rootGapFactor 1 S = 0 ∧ QuarticGapTiltWeight.weight 1 S w = 0 := by
  norm_num [rootGapFactor, QuarticGapTiltWeight.weight, gapCutoff, hS]

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3)
    (hw : fullVorticity u x = 0) :
    rootPatch gamma chi modes u centers tau i x = 0 ∧
    rootVorticity gamma chi modes u centers tau i x = 0 := by
  simp [rootVorticity, rootPatch, hw]

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnergy.ae_coordinate_weighted_rootVorticity_energy_le

#print axioms Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight.weight_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight.weight_le_squaredGapWeight
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight.collisionCost_eq_squared_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight.weight_eq_of_gate_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.QuarticGapTiltWeight.excess_le_weighted_tilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifference.rootPatch_eq_factor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifference.abs_rootPatch_sub_mul_vorticity_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.rootVorticity_eq_factor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.locallyLipschitz_topGap
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.locallyLipschitz_gapCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.locallyLipschitz_rootGapFactor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.gaussianFactor_pos
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.patch_eq_amplitude_mul_gaussianFactor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.rootPatch_sq_eq_gated_patch
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.locallyLipschitz_rootFieldFactor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootVorticity.locallyLipschitz_rootVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifferentiation.continuous_rootFieldFactor
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifferentiation.ae_coordinate_rootVorticity_derivative_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifferentiation.sourceExcess_le_quartic_jointTilt_add_collision
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.rootPatch_fourth_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.sum_rootPatch_fourth
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.continuous_rootPatch
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.continuous_rootVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.ae_differentiable_rootVorticity_lift
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition.exists_local_root_partition
