import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPressureEllipticBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCoordinateDerivatives

/-! Regression and dependency audit for elliptic pressure localization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureEllipticBudgetAudit

open scoped BigOperators RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation
open FourierPressureCommutator FourierPressureEllipticCommutator FourierEllipticProductCoefficients
open FourierEllipticProductEnergy FourierCoordinateDerivatives PancakeAnisotropyDepletion
open PancakeFourierTranslationCurve Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Nonzero input and shift can produce zero output without zero product errors. -/
example :
    let k : Wavevector := ![1, 1, 0]
    let e := (EuclideanSpace.basisFun (Fin 3) ℝ) 0
    ellipticScalarKernel (-k) k = -2 ∧
      ellipticVectorKernel e (-k) k = -(EuclideanSpace.basisFun (Fin 3) ℝ) 1 := by
  dsimp only
  constructor
  · norm_num [ellipticScalarKernel, realFrequency, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  · ext i
    fin_cases i <;> norm_num [ellipticVectorKernel, lineRemainder, realFrequency,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]

example (c : Wavevector → ℂ) : coordinateEnergy {0} c = 0 ∧ secondCoordinateEnergy {0} c = 0 := by
  simp [coordinateEnergy, secondCoordinateEnergy, scalarEnergy, coordinateMultiplier, secondCoordinateMultiplier]

example : coordinateEnergy {(![1, 0, 0] : Wavevector)} (fun _ ↦ Complex.I) = 1 ∧
    secondCoordinateEnergy {(![1, 0, 0] : Wavevector)} (fun _ ↦ Complex.I) = 1 := by
  norm_num [coordinateEnergy, secondCoordinateEnergy, scalarEnergy,
    coordinateMultiplier, secondCoordinateMultiplier, Fin.sum_univ_three]

/-- Both mixed terms and the cutoff-Hessian term survive a complex cutoff. -/
example :
    let A := tensorCoefficient {(![1, 0, 0] : Wavevector)} {![0, 1, 0]}
      (fun _ ↦ Complex.I) (fun _ ↦ 1) ![1, 1, 0]
    A 0 1 = Complex.I ∧ A 1 0 = Complex.I ∧ A 0 0 = Complex.I := by
  norm_num [tensorCoefficient, tensorKernel, Finset.sum_filter, Finset.sum_product]

example : (∫ x : T3, ‖polynomialDerivative {(![1, 0, 0] : Wavevector)} (fun _ ↦ 1) 0 x‖ ^ 2) =
    ‖unitTorusDerivativePhase‖ ^ 2 := by
  rw [integral_polynomialDerivative_sq]
  norm_num [scalarEnergy, coordinateMultiplier]

example :
    (∫ x : T3, ‖deriv (fun t : ℝ ↦ polynomialDerivative {(![1, 1, 0] : Wavevector)}
      (fun _ ↦ 1) 1 (x + coordinateShift 0 t)) 0‖ ^ 2) = ‖unitTorusDerivativePhase‖ ^ 4 := by
  rw [integral_second_polynomialDerivative_sq]
  norm_num [scalarEnergy, secondCoordinateMultiplier]

end Mettapedia.FluidDynamics.NavierStokes.PressureEllipticBudgetAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltEllipticIdentity.norm_sq_smul_tiltSymbol_sub
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.pairing_eq_inner
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.norm_pairing_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.norm_transverse_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.norm_matrixAction_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.transverse_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix.transverse_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierProductEnergy.scalarEnergy_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierProductEnergy.scalarEnergy_convolution_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierProductEnergy.scalarEnergy_convolution_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.realTraceAmplitude_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.complexifyVector_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.complexifyVector_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.trace_mul_symbol_difference
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.commutatorCoefficient_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator.tiltCommutatorEnergy_le_elliptic_products
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.laplaceMultiplier_eq_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.scalarCoefficient_eq_products
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.tensorCoefficient_eq_products
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.complexifyVector_kernel_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.matrixAction_tensorCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.vectorCoefficient_eq_tensor
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients.norm_vectorCoefficient_sq_le_tensor
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy.laplaceEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy.scalarCoefficient_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy.tensorCoefficient_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy.vectorCoefficient_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy.tiltCommutatorEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.fourierField_apply_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.reconstruction_derivativeCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.hasDerivAt_reconstruction_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.polynomialDerivative_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.hasDerivAt_polynomialDerivative_shift
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.integral_polynomialDerivative_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierCoordinateDerivatives.integral_second_polynomialDerivative_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPressureEllipticBudget.norm_potentialCoordinateField_apply_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPressureEllipticBudget.tiltCommutatorEnergy_le_derivative_cost
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPressureEllipticBudget.exists_pressure_elliptic_budget
