import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalNormalVorticityIntegral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalNormalVorticityDiffusion
import Mettapedia.Analysis.RadialPancakeCoherenceTests

/-!
# Normal-vorticity identities and a geometric-forcing check

The finite-dimensional check starts with zero normal vorticity and zero
normal strain quotient. A tilting strain nevertheless creates a nonzero
normal derivative. Thus the geometric forcing cannot be discarded.
It is not asserted to be a spatial Navier–Stokes counterexample.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.NormalVorticityAudit

open Mettapedia.Analysis NormalVorticityEnergy RadialPancakeCoherenceTests
open scoped RealInnerProductSpace

theorem initial_component_zero : component (e 0) (e 2) = 0 := by
  simp [component, inner_e]

theorem normal_strain_zero : ⟪e 2, tilt (e 2)⟫ = 0 := by
  simp [tilt, ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right, inner_e]

theorem tilt_creates_normal_component : rate (e 0) (e 2) (tilt (e 0)) (tilt (e 2)) = 2 := by
  unfold rate
  rw [tilt_normal_action (e 0)]
  simp [component, norm_e, inner_e]

end Mettapedia.FluidDynamics.NavierStokes.NormalVorticityAudit

#print axioms Mettapedia.Analysis.NormalVorticityEnergy.energy_eq
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.energy_nonneg
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.component_single
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.sum_energy_axes
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.abs_component_mul_norm
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.hasDerivAt_component
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.rate_eq_strain_add_forcing
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.forcingNumerator_of_orthogonal
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.square_rate_le
#print axioms Mettapedia.Analysis.NormalVorticityEnergy.abs_le_initial_add_integral
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.abs_amplitudeCurvature_radialOperator_le
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.abs_amplitudeCurvature_tensor_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.normalDefect_orthogonal
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.forcing_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.forcing_eq_nonviscous_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.abs_amplitude_image_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.rate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.hasDerivAt_component_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.absolutelyContinuousOnInterval_component_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.continuousOn_strainQuotient_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.ae_hasDerivAt_component_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.intervalIntegrable_forcing_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.abs_component_le_initial_add_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.integral_projection_mul_second_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.integral_projection_mul_laplacian_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.integral_normal_mul_laplacian_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.integral_normal_mul_laplacian_nonpos
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.squareMaterialRate_eq_nonviscous_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.hasDerivAt_square_component_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.continuous_squareMaterialRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity.integral_squareMaterialRate_add_dissipation_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalVorticityAudit.initial_component_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalVorticityAudit.normal_strain_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalVorticityAudit.tilt_creates_normal_component
