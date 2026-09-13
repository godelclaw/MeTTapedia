import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialMeanChannels
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularDiffusion
import Mettapedia.Analysis.SignedCrossKernelCurvatureSignTests

/-! # Signed radial curvature, mean balance, and tangency checks -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RadialMeanChannelsAudit

open Mettapedia.Analysis SignedCrossKernel SignedCrossKernelCurvatureSignTests
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- A rank-one algebraic example, not a self-consistent fluid solution. -/
theorem tangent_values_leave_curvature :
    ⟪axis 1, direction⟫ = 0 ∧ ⟪axis 1, increment⟫ = 1 ∧
      pairedCurvature 1 (kernel 1) direction direction increment 0 = -2 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [axis, direction, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  · norm_num [axis, increment, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  · norm_num [curvature_value]

/-- Equal normal gradient components suffice at equal tangent endpoint values. -/
theorem equal_normal_derivatives_cancel (N n : ℕ) (e : R3) (he : ‖e‖ = 1)
    {h : R3} (hh : h ≠ 0) (a v w : R3) (ha : ⟪h, a⟫ = 0) (hv : ⟪h, v⟫ = ⟪h, w⟫) :
    pairedCurvature n (RadialRieszRegularization.tensor N h) a a v w = 0 := by
  rw [RadialPancakeCurvature.pairedCurvature_tensor_same_value N n e he hh a v w ha]
  simp [inner_sub_right, hv]

end Mettapedia.FluidDynamics.NavierStokes.RadialMeanChannelsAudit

#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedEndpointRate_add
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedMaterialRate_add_smul_endpoint
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedKernelDiffusion.continuous_diffusionDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedKernelDiffusion.continuous_curvatureDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPairedKernelDiffusion.diffusionSource_eq_neg_curvatureSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularDiffusion.diffusionSource_eq_neg_curvatureSource
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.pairedCurvature_radialOperator
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.radialCurvature_of_plane
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.radialCurvature_eq_zero_of_tangent
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.pairedCurvature_tensor
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.pairedCurvature_tensor_eq_zero_of_tangent
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.pairedCurvature_radial_same_value
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.abs_pairedCurvature_radial_same_value_le
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.pairedCurvature_tensor_same_value
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.hasSum_pairedCurvature
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.hasSum_radialCurvature_images
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.curvatureDensity_eq_images
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.explicitRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.continuous_diffusionRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.integral_diffusionRate_eq_neg_curvatureSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.integrable_nonviscousRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.meanRate_eq_jointRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.ae_meanRate_eq_jointRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.ae_hasDerivAt_source
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.integral_source_eq_initial_add_weighted_channels
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialMeanChannels.tendsto_integral_weighted_jointRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialMeanChannelsAudit.tangent_values_leave_curvature
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialMeanChannelsAudit.equal_normal_derivatives_cancel
