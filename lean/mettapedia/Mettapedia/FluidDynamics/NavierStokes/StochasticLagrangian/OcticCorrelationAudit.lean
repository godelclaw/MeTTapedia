import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticCorrelation

/-!
# A sign check for the proposed correlation correction

Even a positive rank-one operator need not give positive source curvature.
This is an algebraic obstruction to a convexity shortcut, not a vorticity
field or a counterexample to Navier–Stokes regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.OcticCorrelationAudit

open Mettapedia.Analysis.OcticKernelCorrelation
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def axis : R3 := EuclideanSpace.single 0 1
def vector : R3 := WithLp.toLp 2 ![1, 3, 0]
def variation : R3 := WithLp.toLp 2 ![1, -6, 0]
def operator : R3 →L[ℝ] R3 := InnerProductSpace.rankOne ℝ axis axis

theorem operator_nonnegative (x : R3) : 0 ≤ ⟪x, operator x⟫ := by
  simp only [operator, InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm axis x]
  exact mul_self_nonneg _

theorem sourceCurvature_negative : sourceCurvature operator vector variation = -42 := by
  norm_num [sourceCurvature, operator, axis, vector, variation,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, real_inner_smul_right,
    PiLp.inner_apply, Real.inner_apply, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ,
    PiLp.single_apply]

theorem positive_operator_does_not_imply_source_convexity :
    ¬ (∀ (H : R3 →L[ℝ] R3), (∀ x : R3, 0 ≤ ⟪x, H x⟫) →
      ∀ a v : R3, 0 ≤ sourceCurvature H a v) := by
  intro h
  have hc := h operator operator_nonnegative vector variation
  rw [sourceCurvature_negative] at hc
  norm_num at hc

end Mettapedia.FluidDynamics.NavierStokes.OcticCorrelationAudit

#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.continuous_convolution
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.mFourier_add_argument
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.mFourierCoeff_translate
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.mFourierCoeff_convolution
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.integral_norm_sq_le_of_coeff_le
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.integral_norm_convolution_sq_le
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.ofReal_realConvolution
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.continuous_realConvolution
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.integral_realConvolution_sq_le
#print axioms Mettapedia.Analysis.UnitTorusConvolutionEnergy.abs_integral_mul_realConvolution_le
#print axioms Mettapedia.Analysis.UnitTorusKernelCorrelation.integral_quadratic_eq_mean
#print axioms Mettapedia.Analysis.UnitTorusKernelCorrelation.integral_weighted_quadratic_eq_increment
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.hasDerivAt_density
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.materialRate_add_smul_endpoint
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.continuous_density
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.endpointRate_eq_factored
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.hasDerivAt_sourceForm
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.hasDerivAt_sourceRate
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.hasDerivAt_amplitudeRate
#print axioms Mettapedia.Analysis.OcticKernelCorrelation.hasDerivAt_endpointRate
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_rieszEntry_le_one
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.continuous_entry
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.norm_mFourierCoeff_re_entry_le_one
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_re_entry_convolution_sq_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_quarticTensorEntry_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.continuous_quarticTensorEntry
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_correlationEntry_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_octicCorrelation_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.octic_correction_bounds
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_quadratic_tensor_eq_zero
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.integral_weighted_quadratic_tensor_eq_increment
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.bilinear_tensor_eq_sum
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.quadratic_tensor_eq_sum
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.octicCorrelation_eq_pairIntegral
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.hasDerivAt_quarticTensorEntry
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.hasDerivAt_quarticAmplitude
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_quarticAmplitudeRate_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_quarticTensorRate_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.continuous_quarticTensorRate
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.continuous_quarticAmplitudeRate
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_mixedGradientEntry_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.abs_mixedGradientSum_le
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.sourceRate_tensor_eq_sum
#print axioms Mettapedia.Analysis.PeriodicRadialRiesz.mixedGradientSum_eq_pairIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.eighthMoment_eq_meanEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.abs_correlation_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.corrected_energy_bounds
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.correlation_eq_pairIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.hasDerivAt_pairDensity_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.periodicRate_split_viscosity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.abs_mixedGradientContribution_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.mixedGradientContribution_eq_pairIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation.hasDerivAt_endpointRate_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.OcticCorrelationAudit.operator_nonnegative
#print axioms Mettapedia.FluidDynamics.NavierStokes.OcticCorrelationAudit.sourceCurvature_negative
#print axioms Mettapedia.FluidDynamics.NavierStokes.OcticCorrelationAudit.positive_operator_does_not_imply_source_convexity
