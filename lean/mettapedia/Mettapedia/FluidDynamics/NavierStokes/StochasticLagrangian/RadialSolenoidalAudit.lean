import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialCurvatureChannels
import Mettapedia.Analysis.RadialAmplitudeCurvature

/-!
# Solenoidal cancellation and retained amplitude checks

The algebraic tests use a longitudinal positive rank-one operator and a
transverse increment. Its isotropic contribution vanishes, but the amplitude
contribution has either sign. These are symbol-level examples, not periodic
Navier–Stokes solutions or counterexamples to an integrated estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit

open Mettapedia.Analysis SignedCrossKernel EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def axis : R3 := EuclideanSpace.single 0 1
def background : R3 := WithLp.toLp 2 ![1, 1, 0]
def increment (c : ℝ) : R3 := WithLp.toLp 2 ![0, 1, c]
def longitudinal : R3 →L[ℝ] R3 := InnerProductSpace.rankOne ℝ axis axis

theorem longitudinal_nonneg (v : R3) : 0 ≤ ⟪v, longitudinal v⟫ := by
  simp only [longitudinal, InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm axis v]
  exact mul_self_nonneg _

theorem longitudinal_increment_eq_zero (c : ℝ) : longitudinal (increment c) = 0 := by
  norm_num [longitudinal, InnerProductSpace.rankOne_apply, axis, increment,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

theorem amplitude_value (c : ℝ) : amplitudeCurvature 1 longitudinal background (increment c) 0 = -48 * c := by
  have hn : ‖background‖ ^ 2 = 2 := by
    norm_num [background, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  have hn4 : ‖background‖ ^ 4 = 4 := by nlinarith [sq_nonneg (‖background‖ ^ 2 - 2)]
  unfold amplitudeCurvature
  rw [show 2 * (1 + 1) = 4 by norm_num, hn4]
  norm_num [background, increment, longitudinal, axis,
    cross, cross_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem frozen_curvature_value (c : ℝ) :
    pairedCurvature 1 longitudinal background background (increment c) 0 = -48 * c := by
  rw [pairedCurvature_same_value_eq_channels]
  simp only [sub_zero, longitudinal_increment_eq_zero, inner_zero_right, mul_zero,
    zero_add, amplitude_value]

theorem amplitude_has_both_signs :
    pairedCurvature 1 longitudinal background background (increment 1) 0 < 0 ∧
      0 < pairedCurvature 1 longitudinal background background (increment (-1)) 0 := by
  norm_num [frozen_curvature_value]

end Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit

#print axioms Mettapedia.Analysis.EuclideanCrossProduct.cross_sub_left
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.cross_sub_right
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.tensor_neg
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_re_entry_eq_zero
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_tensor_eq_zero
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.sum_symbol_mul_eq_zero
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_tensor_realPart_eq_zero
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedCurvature_same_value_eq_channels
#print axioms Mettapedia.Analysis.SignedCrossKernel.pairedCurvature_eq_frozen_add_remainder
#print axioms Mettapedia.Analysis.SignedCrossKernel.endpointCurvatureRemainder_same_value
#print axioms Mettapedia.Analysis.SignedCrossKernel.continuous_amplitudeCurvature
#print axioms Mettapedia.Analysis.SignedCrossKernel.continuous_endpointCurvatureRemainder
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.amplitudeCurvature_radialOperator
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.amplitudeCurvature_radialOperator_eq_zero_of_tangent
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.amplitudeCurvature_tensor
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.amplitudeCurvature_tensor_eq_zero_of_tangent
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.hasSum_amplitudeCurvature
#print axioms Mettapedia.Analysis.RadialPancakeCurvature.hasSum_amplitudeCurvature_images
#print axioms Mettapedia.Analysis.SolenoidalCrossIncrement.integral_kernel_increment_eq_zero
#print axioms Mettapedia.Analysis.SolenoidalCrossIncrement.integral_inner_cross_increment_eq_zero
#print axioms Mettapedia.Analysis.SolenoidalCrossIncrement.integral_cross_increment_eq_background_increment
#print axioms Mettapedia.Analysis.SolenoidalCrossIncrement.integral_cross_increment_constant_eq_zero
#print axioms Mettapedia.Analysis.SolenoidalCrossIncrement.integral_pairedCurvature_eq_channels
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.integral_tensor_fullFourierField_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.integral_tensor_fullVorticity_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.derivative_curl_transverse
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.integral_tensor_fullCurlGradient_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.integral_gradient_cross_eq_background_increment
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialSolenoidal.integral_gradient_cross_constant_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.amplitudeDensity_eq_images
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.continuous_backgroundDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.continuous_amplitudeDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.continuous_endpointDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.integral_curvature_eq_channels
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.curvatureSource_eq_reducedCurvatureSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalRadialCurvatureChannels.jointRate_eq_reduced_channels
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit.longitudinal_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit.longitudinal_increment_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit.amplitude_value
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit.frozen_curvature_value
#print axioms Mettapedia.FluidDynamics.NavierStokes.RadialSolenoidalAudit.amplitude_has_both_signs
