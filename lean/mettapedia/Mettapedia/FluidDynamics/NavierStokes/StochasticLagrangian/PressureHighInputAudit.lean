import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputJointSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootHighInputBudget

/-! High-input aggregation, pointwise reconstruction, and exact complement audits. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureHighInputAction PressureHighInputFourier
open PressureHighInputComplement PressureOperatorCoordinates PressureBilinearOperator
open ComplexPressurePair PressureTiltSymbol PancakeAnisotropyDepletion
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open Mettapedia.Analysis.UnitTorusContinuousFourier
open Mettapedia.Analysis.EuclideanBilinearCoordinates Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem transition_half : outputMultiplier 640 ![3, 4, 0] = 1 / 2 := by
  apply Mettapedia.Analysis.DyadicLowPass.multiplier_eq_half_of_norm_eq_two
  have h : ‖(256 / 640 : ℝ) • realFrequency ![3, 4, 0]‖ ^ 2 = 4 := by
    norm_num [realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  nlinarith [norm_nonneg ((256 / 640 : ℝ) • realFrequency ![3, 4, 0])]

private theorem high_zero : inputMultiplier 640 0 ![1280, 0, 0] = 1 := by
  apply Mettapedia.Analysis.DyadicHighPass.multiplier_eq_one_of_le_norm
  have he : (inputScale 640 0)⁻¹ • realFrequency ![1280, 0, 0] =
      EuclideanSpace.single 0 (2 : ℝ) := by
    ext i
    fin_cases i <;> norm_num [inputScale, realFrequency]
  rw [he]
  norm_num

private theorem high_one : inputMultiplier 640 1 ![1280, 0, 0] = 1 / 2 := by
  apply Mettapedia.Analysis.DyadicHighPass.multiplier_eq_half_of_norm_eq_one
  have he : (inputScale 640 1)⁻¹ • realFrequency ![1280, 0, 0] =
      EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i <;> norm_num [inputScale, realFrequency]
  rw [he]
  simp

private theorem pair_entry :
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = (-192 / 40768625 : ℂ) := by
  rw [entry_pressurePairOperator]
  norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
    lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

private theorem output_eq : (![3, 4, 0] : Wavevector) =
    ![1280, 0, 0] + ![-1277, 4, 0] := by
  ext i
  fin_cases i <;> norm_num

/-- The complete high-input sum restores the full input weight. -/
example : (coefficientCLM ![3, 4, 0]
    (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single 0 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (-96 / 40768625 : ℂ) := by
  rw [coefficient_tailOperator_modes _ _ _ _ (by simp), if_pos output_eq,
    transition_half, high_zero]
  change ((1 / 2 : ℝ) : ℂ) * ((1 : ℂ) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2) = _
  rw [pair_entry]
  norm_num

/-- Raising the input threshold retains only half of this input interaction. -/
example : (coefficientCLM ![3, 4, 0]
    (tailOperator 640 (by norm_num) 1 (EuclideanSpace.single 0 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (-48 / 40768625 : ℂ) := by
  rw [coefficient_tailOperator_modes _ _ _ _ (by simp), if_pos output_eq,
    transition_half, high_one]
  change ((1 / 2 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2) = _
  rw [pair_entry]
  norm_num

/-- Reconstruction evaluates the actual continuous operator at a spatial point. -/
example : (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single 0 1)
    (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
    (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ)))) (0 : T3) 1 =
      (-96 / 40768625 : ℂ) := by
  rw [tailOperator_modes _ _ _ _ (by simp), ← output_eq, transition_half, high_zero]
  simp only [modeField, ContinuousMap.coe_mk, UnitAddTorus.mFourier, Pi.zero_apply,
    fourier_eval_zero, Finset.prod_const_one, one_smul]
  change ((1 / 2 : ℝ) : ℂ) * ((1 : ℂ) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2) = _
  rw [pair_entry]
  norm_num

/-- The complementary input sector changes with the threshold; it is not discarded. -/
example : lowInputMultiplier 640 0 ![1280, 0, 0] = 0 ∧
    lowInputMultiplier 640 1 ![1280, 0, 0] = 1 / 2 := by
  rw [lowInputMultiplier, high_zero, lowInputMultiplier, high_one]
  norm_num

/-- Frequencies outside the explicit finite input box contribute nothing to the complement. -/
example (N : ℝ) (hN : 0 < N) (J : ℕ) (k : Wavevector)
    (hk : k ∉ lowInputModes N J) : lowInputMultiplier N J k = 0 :=
  lowInputMultiplier_eq_zero_of_not_mem N hN J k hk

/-- Zero output is harmless for arbitrary absolutely convergent input fields. -/
example (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) :
    UnitAddTorus.mFourierCoeff
      (tailOperator N hN J e (fullFourierField id a) (fullFourierField id b)) 0 = 0 := by
  have hz : realFrequency (0 : Wavevector) = 0 := by ext i; simp [realFrequency]
  have ht : complexTiltSymbol e (0 : Wavevector) = 0 := by
    rw [complexTiltSymbol, hz, tiltSymbol_zero]
    rfl
  rw [mFourierCoeff_tailOperator N hN J e he a b ha hb 0]
  simp [pressurePairOperator_apply, tiltPair, ht]

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction.outputMultiplier_eq_zero_of_not_mem
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction.operator_eq_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction.operator_vorticity_eq_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction.transverse_pressure_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputJointSource.jointTilt_eq_fixed_output
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction.hasSum_inputCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction.exists_uniform_fixed_operator_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction.exists_uniform_tail_operator_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction.summable_operators
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction.hasSum_tailOperator_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier.coefficient_tailOperator_modes
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier.hasSum_tailOperator_fourierPairs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier.tailOperator_modes
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier.mFourierCoeff_tailOperator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.lowInputMultiplier_eq_lowPass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.lowInputMultiplier_eq_zero_of_le_norm
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.lowInputMultiplier_eq_zero_of_not_mem
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.lowInputCoefficient_eq_tsum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.high_add_low_coefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.mFourierCoeff_tailOperator_vorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement.tiltCoefficient_eq_tail_add_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource.tailOperator_vorticity_eq_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource.tiltPolynomial_eq_tail_add_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource.transverse_pressure_eq_tail_add_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource.jointTilt_eq_high_input
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputLocalization.hasSum_tailLocalization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputLocalization.finite_tailLocalization_spatial_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootHighInputBudget.exists_uniform_root_budget
