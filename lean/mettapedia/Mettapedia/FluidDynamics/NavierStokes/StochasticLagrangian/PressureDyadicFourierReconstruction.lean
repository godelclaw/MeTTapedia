import Mettapedia.Analysis.BilinearSeries
import Mettapedia.Analysis.UnitTorusContinuousFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicBilinearAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierDerivative

/-!
# Exact low-output coefficients of the full-field dyadic pressure action

Absolute convergence of both input Fourier series permits bilinear
reconstruction in the continuous-field norm. Coefficient extraction then
identifies the complete output-band sum on the low-output ball, with the
normalized input annulus retained. No restriction is imposed on individual
input pairs, and no complementary pressure sector is discarded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator
open FourierPressureTraceSymbol
open PressureDyadicBilinearAction PressureDyadicPeriodization PressureBilinearOperator
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel (physicalCutoff)
open PressureLowOutputDyadicBudget (dyadicParameter)
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

theorem bandOperator_modes (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (u v : C3) :
    bandOperator N hN t e (modeField k u) (modeField p v) =
      modeField (k + p)
        ((physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
          pressurePairOperator e he k p u v) := by
  apply ContinuousMap.ext
  intro x
  change PressureKernelAction.kernelAction (periodicKernel N hN t e)
    (fun y ↦ UnitAddTorus.mFourier k y • u) (fun y ↦ UnitAddTorus.mFourier p y • v) x = _
  rw [PressureDyadicAction.kernelAction_monomials N hN t e he]
  exact congrArg (fun c : ℂ ↦ c • _) UnitAddTorus.mFourier_add.symm

theorem coefficient_sumOperator_modes_low (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (q : Wavevector) (hq : ‖realFrequency q‖ ≤ N / 256) (k p : Wavevector) (u v : C3) :
    coefficientCLM q (sumOperator N hN e (modeField k u) (modeField p v)) =
      if q = k + p then
        (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) • pressurePairOperator e he k p u v
      else 0 := by
  classical
  have hs : HasSum (fun n : ℕ ↦ coefficientCLM q
      (bandOperator N hN (dyadicParameter n) e (modeField k u) (modeField p v)))
      (coefficientCLM q (sumOperator N hN e (modeField k u) (modeField p v))) := by
    rw [sumOperator_apply N hN e he]
    exact (coefficientCLM q).hasSum
      (PressureDyadicAction.summable_action N hN e he (modeField k u) (modeField p v)).hasSum
  have hm (n : ℕ) : coefficientCLM q
      (bandOperator N hN (dyadicParameter n) e (modeField k u) (modeField p v)) =
      if q = k + p then
        (physicalCutoff (dyadicParameter n)
          (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
            pressurePairOperator e he k p u v else 0 := by
    rw [bandOperator_modes N hN (dyadicParameter n) e he]
    exact mFourierCoeff_monomial q (k + p) _
  simp only [hm] at hs
  by_cases hqp : q = k + p
  · simp only [hqp, if_true] at hs ⊢
    have hsmall : ‖realFrequency k + realFrequency p‖ ≤ N / 256 := by
      simpa only [hqp, realFrequency_add] using hq
    have ht := (ContinuousLinearMap.apply ℂ C3 v).hasSum
      ((ContinuousLinearMap.apply ℂ (C3 →L[ℂ] C3) u).hasSum
        (hasSum_mFourierCoeff_periodicKernel N hN e he k p hsmall))
    simp only [mFourierCoeff_periodicKernel N hN _ e he,
      ContinuousLinearMap.apply_apply, smul_apply] at ht
    exact hs.unique ht
  · simp only [hqp, if_false] at hs ⊢
    exact hs.unique hasSum_zero

theorem hasSum_sumOperator_fourierPairs (N : ℝ) (hN : 0 < N) (e : R3)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) :
    HasSum (fun kp : Wavevector × Wavevector ↦
      sumOperator N hN e (modeField kp.1 (a kp.1)) (modeField kp.2 (b kp.2)))
      (sumOperator N hN e (fullFourierField id a) (fullFourierField id b)) := by
  have hfa : Summable (fun k ↦ ‖modeField k (a k)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_modeField_le k (a k)) ha
  have hfb : Summable (fun p ↦ ‖modeField p (b p)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ norm_modeField_le p (b p)) hb
  exact Mettapedia.Analysis.BilinearSeries.hasSum_apply (sumOperator N hN e)
    (fun k ↦ modeField k (a k)) (fun p ↦ modeField p (b p)) hfa hfb

/-- The low-output coefficient is the exact normalized-annulus convolution
of both full input fields, not a finite-mode surrogate. -/
theorem mFourierCoeff_sumAction_low (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun p ↦ ‖b p‖)) (q : Wavevector) (hq : ‖realFrequency q‖ ≤ N / 256) :
    UnitAddTorus.mFourierCoeff
      (PressureDyadicAction.sumAction N hN e (fullFourierField id a) (fullFourierField id b)) q =
      ∑' k, (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
        pressurePairOperator e he k (q - k) (a k) (b (q - k)) := by
  classical
  have hs := (coefficientCLM q).hasSum (hasSum_sumOperator_fourierPairs N hN e a b ha hb)
  simp only [coefficient_sumOperator_modes_low N hN e he q hq] at hs
  rw [← sumOperator_apply N hN e he]
  change coefficientCLM q (sumOperator N hN e _ _) = _
  rw [← hs.tsum_eq, hs.summable.tsum_prod]
  apply tsum_congr
  intro k
  have heq (p : Wavevector) : q = k + p ↔ p = q - k := by
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      rw [h]
      abel
  simp only [heq]
  exact tsum_ite_eq (q - k) _

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction
