import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputReconstruction

/-! Regression tests for actual two-input localization and its spatial weight. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputAudit

open scoped BigOperators
open PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressurePair ComplexPressureConvolution PressureBilinearLocalization
open PressureTwoInputLocalization PressureTwoInputEnergy
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

/-- A frequency shift can create a nonzero mean from an original nonzero mode. -/
example (p : Wavevector) (w : FourierVelocity) :
    finiteCutoffConvolutionCoeff {-p} {p} (fun _ ↦ 1) w 0 = w p := by
  simp only [finiteCutoffConvolutionCoeff, Finset.sum_filter, Finset.sum_product,
    Finset.sum_singleton, neg_add_cancel, ite_true, one_smul]

/-- Multiplication can create divergence even when the original mode is transverse. -/
example : modeDot ![1, 0, 0] ![0, 0, 1] = 0 ∧
    modeDot ![1, 0, 1]
      (finiteCutoffConvolutionCoeff {![0, 0, 1]} {![1, 0, 0]}
        (fun _ ↦ 1) (fun _ ↦ ![0, 0, 1]) ![1, 0, 1]) = 1 := by
  simp only [finiteCutoffConvolutionCoeff, Finset.sum_filter, Finset.sum_product, Finset.sum_singleton]
  norm_num [modeDot, Fin.sum_univ_three, show (![0, 0, 1] : Wavevector) + ![1, 0, 0] = ![1, 0, 1] by decide]

/-- Two constant half cutoffs quarter the output, not halve it. -/
example (e : R3) (p k : Wavevector) (w v : FourierVelocity) :
    doublyLocalizedOutput e {0} {0} {p} {k} (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) w v (p + k) =
      (1 / 4 : ℂ) • tiltPair e p k (w p) (v k) := by
  simp only [doublyLocalizedOutput, localizedOutput, vectorConvolution,
    finiteCutoffOutputModes, pairConvolution, Finset.singleton_product_singleton,
    Finset.image_singleton, Finset.sum_filter, Finset.sum_singleton, zero_add, ite_true, smul_smul]
  norm_num

/-- The two localized inputs carry the independently shifted frequencies. -/
example (e : R3) (a b p k : Wavevector) (w v : FourierVelocity) :
    localizedInputs e {a} {b} {p} {k} (fun _ ↦ 1) (fun _ ↦ 1) w v (b + p + (a + k)) =
      tiltPair e (b + p) (a + k) (w p) (v k) := by
  simp only [localizedInputs, pairConvolution, finiteCutoffOutputModes, finiteCutoffConvolutionCoeff,
    Finset.singleton_product_singleton, Finset.image_singleton, Finset.sum_filter,
    Finset.sum_singleton, ite_true, one_smul]

/-- The quadratic and quartic energy weights differ already for a constant patch. -/
example : ‖(1 / 2 : ℂ)‖ ^ 4 = (1 / 16 : ℝ) ∧
    ‖(1 / 2 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) ∧ (1 / 16 : ℝ) < 1 / 4 := by norm_num

end Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra.finiteCutoffOutputModes_comm
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra.finiteCutoffOutputModes_assoc
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra.pairConvolution_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra.coefficientVec_cutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra.sum_norm_cutoff_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputLocalization.doublyLocalizedOutput_sub_localizedInputs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputEnergy.twoInputCommutator_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputEnergy.doublyLocalizedOutput_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical.doublyLocalizedPressure_eq_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical.doublyLocalizedPressure_add_localizedInputs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical.twoInputCost_fourierCurl_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputPhysical.twoInputCommutator_energy_le_physical_gradient
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.vectorPolynomial_eq_coefficientReconstruction
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.integral_vectorPolynomial_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.vectorPolynomial_convolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.doublyLocalizedOutput_polynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.doublyLocalizedOutput_energy_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction.same_cutoff_energy_eq_integral_fourth_power
