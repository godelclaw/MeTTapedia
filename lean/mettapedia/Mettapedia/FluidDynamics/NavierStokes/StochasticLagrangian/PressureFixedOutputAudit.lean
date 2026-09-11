import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputPhysical
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootFixedOutputBudget

/-! Fixed-output transition, nonzero matched input index, zero output, and tail audits. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureFixedOutputAction PressureOperatorCoordinates
open PressureBilinearOperator ComplexPressurePair PressureTiltSymbol PancakeAnisotropyDepletion
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open Mettapedia.Analysis.UnitTorusContinuousFourier Mettapedia.Analysis.DyadicAnnulus
open Mettapedia.Analysis.DyadicLowPass Mettapedia.Analysis.EuclideanBilinearCoordinates
open Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem transition_half : outputMultiplier 640 ![3, 4, 0] = 1 / 2 := by
  apply multiplier_eq_half_of_norm_eq_two
  have h : ‖(256 / 640 : ℝ) • realFrequency ![3, 4, 0]‖ ^ 2 = 4 := by
    norm_num [realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  nlinarith [norm_nonneg ((256 / 640 : ℝ) • realFrequency ![3, 4, 0])]

private theorem input_half :
    normalizedCutoff ((inputScale 640 1)⁻¹ • realFrequency ![1280, 0, 0]) = 1 / 2 := by
  apply normalizedCutoff_eq_half_of_norm_eq_one
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

/-- At input index one, a transition output retains both half-weights. -/
example : (coefficientCLM ![3, 4, 0]
    (operator 640 (by norm_num) 1 (EuclideanSpace.single 0 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (-48 / 40768625 : ℂ) := by
  rw [coefficient_operator_modes _ _ _ _ (by simp)]
  have hq : (![3, 4, 0] : Wavevector) = ![1280, 0, 0] + ![-1277, 4, 0] := by
    ext i
    fin_cases i <;> norm_num
  rw [if_pos hq, transition_half, input_half]
  change ((1 / 2 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2) = _
  rw [pair_entry]
  norm_num

example : outputMultiplier 640 ![3, 4, 0] ≠ 1 := by rw [transition_half]; norm_num

/-- Outputs beyond the fixed filter vanish at every input index. -/
example (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) (q : Wavevector) (hq : N / 64 ≤ ‖realFrequency q‖) :
    UnitAddTorus.mFourierCoeff
      (operator N hN j e (fullFourierField id a) (fullFourierField id b)) q = 0 := by
  rw [mFourierCoeff_operator N hN j e he a b ha hb q, outputMultiplier_eq_zero N hN q hq]
  simp

/-- Filling the zero mode of the filter does not introduce a pressure-tilt mean. -/
example (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) :
    UnitAddTorus.mFourierCoeff
      (operator N hN j e (fullFourierField id a) (fullFourierField id b)) 0 = 0 := by
  have hz : realFrequency (0 : Wavevector) = 0 := by ext i; simp [realFrequency]
  have ht : complexTiltSymbol e (0 : Wavevector) = 0 := by
    rw [complexTiltSymbol, hz, tiltSymbol_zero]
    rfl
  rw [mFourierCoeff_operator N hN j e he a b ha hb 0]
  simp [pressurePairOperator_apply, tiltPair, ht]

example : PressureLowOutputCutoff.ratio (PressureLowOutputDyadicBudget.dyadicParameter (3 + 2)) /
    inputScale 1024 3 = (1 / 67108864 : ℝ) := by
  rw [ratio_div_inputScale]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol.outputMultiplier_eq_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol.outputMultiplier_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol.physicalCutoff_matched
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol.ratio_sq_matched
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol.ratio_div_inputScale
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputEnvelope.exists_uniform_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.summable_operator_bands
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.hasSum_operator_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.hasSum_matched_pair
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.coefficient_operator_modes
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.hasSum_operator_fourierPairs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction.mFourierCoeff_operator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputPhysical.mFourierCoeff_operator_vorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputPhysical.tiltCoefficient_eq_operator_add_complement
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputLocalization.hasSum_localization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputLocalization.finite_localization_spatial_norm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget.sumAction_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget.sumActionNorm_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget.exists_uniform_band_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget.exists_uniform_tail_budget
