import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputAction
import Mettapedia.Analysis.UnitTorusFourierUniqueness

/-! Every Fourier coefficient of the complete high-input pressure operator. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureFixedOutputAction PressureHighInputAction PressureBilinearOperator
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open Mettapedia.Analysis.UnitTorusContinuousFourier Mettapedia.Analysis.DyadicAnnulus

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Field" => C(T3, C3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : NormedAddCommGroup (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem coefficient_tailOperator_modes (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (q k p : Wavevector) (u v : C3) :
    coefficientCLM q (tailOperator N hN J e (modeField k u) (modeField p v)) =
      if q = k + p then (outputMultiplier N q : ℂ) • (inputMultiplier N J k : ℂ) •
        pressurePairOperator e he k p u v else 0 := by
  classical
  have hs := (coefficientCLM q).hasSum
    (hasSum_tailOperator_apply N hN J e he (modeField k u) (modeField p v))
  simp only [coefficient_operator_modes N hN _ e he q] at hs
  by_cases hqp : q = k + p
  · simp only [if_pos hqp] at hs ⊢
    have ht := ((hasSum_inputCutoff N J k).smul_const (pressurePairOperator e he k p u v)).const_smul
      (outputMultiplier N q : ℂ)
    apply hs.unique
    simpa only [Complex.coe_smul] using ht
  · simp only [if_neg hqp] at hs ⊢
    exact hs.unique hasSum_zero

theorem hasSum_tailOperator_fourierPairs (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) :
    HasSum (fun kp : Wavevector × Wavevector ↦
      tailOperator N hN J e (modeField kp.1 (a kp.1)) (modeField kp.2 (b kp.2)))
      (tailOperator N hN J e (fullFourierField id a) (fullFourierField id b)) := by
  have hfa : Summable (fun k ↦ ‖modeField k (a k)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_modeField_le k (a k)) ha
  have hfb : Summable (fun p ↦ ‖modeField p (b p)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ norm_modeField_le p (b p)) hb
  exact Mettapedia.Analysis.BilinearSeries.hasSum_apply (tailOperator N hN J e)
    (fun k ↦ modeField k (a k)) (fun p ↦ modeField p (b p)) hfa hfb

theorem tailOperator_modes (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (u v : C3) :
    tailOperator N hN J e (modeField k u) (modeField p v) =
      modeField (k + p) ((outputMultiplier N (k + p) : ℂ) • (inputMultiplier N J k : ℂ) •
        pressurePairOperator e he k p u v) := by
  apply Mettapedia.Analysis.UnitTorusFourierUniqueness.eq_of_mFourierCoeff_eq
  intro q
  change coefficientCLM q (tailOperator N hN J e (modeField k u) (modeField p v)) =
    UnitAddTorus.mFourierCoeff (fun x : T3 ↦ UnitAddTorus.mFourier (k + p) x •
      ((outputMultiplier N (k + p) : ℂ) • (inputMultiplier N J k : ℂ) •
        pressurePairOperator e he k p u v)) q
  rw [coefficient_tailOperator_modes N hN J e he q k p u v, mFourierCoeff_monomial]
  split_ifs with hq
  · rw [hq]
  · rfl

theorem mFourierCoeff_tailOperator (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff
      (tailOperator N hN J e (fullFourierField id a) (fullFourierField id b)) q =
      ∑' k, (outputMultiplier N q : ℂ) • (inputMultiplier N J k : ℂ) •
        pressurePairOperator e he k (q - k) (a k) (b (q - k)) := by
  classical
  have hs := (coefficientCLM q).hasSum (hasSum_tailOperator_fourierPairs N hN J e a b ha hb)
  simp only [coefficient_tailOperator_modes N hN J e he q] at hs
  change coefficientCLM q (tailOperator N hN J e _ _) = _
  rw [← hs.tsum_eq, hs.summable.tsum_prod]
  apply tsum_congr
  intro k
  have heq (p : Wavevector) : q = k + p ↔ p = q - k := by
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [h]; abel
  simp only [heq]
  exact tsum_ite_eq (q - k) _

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputFourier
