import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicFourierReconstruction

/-!
# The pressure action with a fixed low-pass output filter

Matched input and output indices define a convergent bilinear operator
series. Every Fourier coefficient is identified, including zero and the
transition region of the output filter. Both input fields are unrestricted
absolutely convergent Fourier series.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureDyadicBilinearAction PressureDyadicFourierReconstruction
open PressureBilinearOperator PressureLowOutputDyadicBudget PressureTiltSymbol ComplexPressurePair
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel (physicalCutoff)
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open Mettapedia.Analysis.UnitTorusContinuousFourier Mettapedia.Analysis.DyadicAnnulus

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Field" => C(T3, C3)
local notation "FieldOp" => Field →L[ℂ] Field →L[ℂ] Field

local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : NormedAddCommGroup (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace (Field →L[ℂ] Field) := ContinuousLinearMap.instCompleteSpace
local instance : NormedAddCommGroup FieldOp := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ FieldOp := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace FieldOp := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def operator (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) : FieldOp :=
  ∑' m : ℕ, bandOperator (inputScale N j) (inputScale_pos N hN j)
    (dyadicParameter (j + m)) e

theorem summable_operator_bands (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1) :
    Summable (fun m : ℕ ↦ bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e) :=
  (summable_bandOperator (inputScale N j) (inputScale_pos N hN j) e he).comp_injective
    (show Function.Injective (fun m : ℕ ↦ j + m) from fun _ _ h ↦ Nat.add_left_cancel h)

set_option maxHeartbeats 800000 in
theorem hasSum_operator_apply (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (f g : Field) :
    HasSum (fun m : ℕ ↦ bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e f g) (operator N hN j e f g) := by
  have hs : HasSum (fun m : ℕ ↦ bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e) (operator N hN j e) :=
    (summable_operator_bands N hN j e he).hasSum
  exact (ContinuousLinearMap.apply ℂ Field g).hasSum
    ((ContinuousLinearMap.apply ℂ (Field →L[ℂ] Field) f).hasSum
      hs)

theorem hasSum_matched_pair (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (u v : C3) :
    HasSum (fun m : ℕ ↦
      (physicalCutoff (dyadicParameter (j + m))
        ((inputScale N j)⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
          pressurePairOperator e he k p u v)
      ((outputMultiplier N (k + p) : ℂ) •
        (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
          pressurePairOperator e he k p u v) := by
  have hz : (256 / N : ℝ) • realFrequency (k + p) = 0 →
      (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
        pressurePairOperator e he k p u v = 0 := by
    intro h
    have hf : realFrequency (k + p) = 0 :=
      (smul_eq_zero.mp h).resolve_left (div_ne_zero (by norm_num) hN.ne')
    have ht : complexTiltSymbol e (k + p) = 0 := by
      rw [complexTiltSymbol, hf, tiltSymbol_zero]
      rfl
    simp [pressurePairOperator_apply, tiltPair, ht]
  have hs := Mettapedia.Analysis.DyadicLowPass.hasSum_smul
    ((normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
      pressurePairOperator e he k p u v) hz
  simp_rw [physicalCutoff_matched,
    mul_comm (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k)),
    Complex.ofReal_mul, mul_smul, Complex.coe_smul]
  exact hs

theorem coefficient_operator_modes (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (q k p : Wavevector) (u v : C3) :
    coefficientCLM q (operator N hN j e (modeField k u) (modeField p v)) =
      if q = k + p then (outputMultiplier N q : ℂ) •
        (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
          pressurePairOperator e he k p u v else 0 := by
  classical
  have hs := (coefficientCLM q).hasSum
    (hasSum_operator_apply N hN j e he (modeField k u) (modeField p v))
  have hm (m : ℕ) : coefficientCLM q
      (bandOperator (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m)) e
        (modeField k u) (modeField p v)) =
      if q = k + p then
        (physicalCutoff (dyadicParameter (j + m))
          ((inputScale N j)⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
            pressurePairOperator e he k p u v else 0 := by
    rw [bandOperator_modes _ _ _ e he]
    exact mFourierCoeff_monomial q (k + p) _
  simp only [hm] at hs
  by_cases hqp : q = k + p
  · simp only [hqp, if_true] at hs ⊢
    exact hs.unique (hasSum_matched_pair N hN j e he k p u v)
  · simp only [hqp, if_false] at hs ⊢
    exact hs.unique hasSum_zero

theorem hasSum_operator_fourierPairs (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) :
    HasSum (fun kp : Wavevector × Wavevector ↦
      operator N hN j e (modeField kp.1 (a kp.1)) (modeField kp.2 (b kp.2)))
      (operator N hN j e (fullFourierField id a) (fullFourierField id b)) := by
  have hfa : Summable (fun k ↦ ‖modeField k (a k)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_modeField_le k (a k)) ha
  have hfb : Summable (fun p ↦ ‖modeField p (b p)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ norm_modeField_le p (b p)) hb
  exact Mettapedia.Analysis.BilinearSeries.hasSum_apply (operator N hN j e)
    (fun k ↦ modeField k (a k)) (fun p ↦ modeField p (b p)) hfa hfb

/-- Exact fixed-filter coefficient at every output frequency. -/
theorem mFourierCoeff_operator (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff
      (operator N hN j e (fullFourierField id a) (fullFourierField id b)) q =
      ∑' k, (outputMultiplier N q : ℂ) •
        (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
          pressurePairOperator e he k (q - k) (a k) (b (q - k)) := by
  classical
  have hs := (coefficientCLM q).hasSum (hasSum_operator_fourierPairs N hN j e a b ha hb)
  simp only [coefficient_operator_modes N hN j e he q] at hs
  change coefficientCLM q (operator N hN j e _ _) = _
  rw [← hs.tsum_eq, hs.summable.tsum_prod]
  apply tsum_congr
  intro k
  have heq (p : Wavevector) : q = k + p ↔ p = q - k := by
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [h]; abel
  simp only [heq]
  exact tsum_ite_eq (q - k) _

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputAction
