import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicOperatorKernel
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Periodic exact-partition pressure kernels

The actual complex pressure kernels descend to the unit six-torus with exact
Fourier coefficients. Their mass and wrapped first moment retain the output
ratio gains and the input-scale factor, with no additional periodization cost.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open FrequencyPairPeriodization PressureDyadicOperatorKernel PressureBilinearOperator
open PressureLowOutputCutoff (ratio)
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel (physicalCutoff)
open PressureLowOutputDyadicBudget
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) : T6 → Op :=
  periodize (operatorKernel N hN t e)

theorem measurable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) :
    Measurable (periodicKernel N hN t e) :=
  measurable_periodize _ (operatorKernel N hN t e).continuous.measurable

theorem integrable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) :
    Integrable (periodicKernel N hN t e) := integrable_periodize _

theorem mFourierCoeff_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) :
    UnitAddTorus.mFourierCoeff (periodicKernel N hN t e) (pairWavevector k p) =
      (physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
        pressurePairOperator e he k p := by
  rw [periodicKernel, mFourierCoeff_periodize _ (operatorKernel N hN t e).continuous.measurable
    (operatorKernel N hN t e).integrable, ← SchwartzMap.fourier_coe]
  have hfreq : euclideanFrequencyPairOfWavevector (pairWavevector k p) =
      pairEquiv.symm (realFrequency k, realFrequency p) := by
    ext i
    fin_cases i <;> rfl
  rw [hfreq]
  exact fourier_operatorKernel N hN t e he k p

theorem integrable_moment_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (m : ℕ) :
    Integrable (fun q : T6 ↦ ‖q‖ ^ m * ‖periodicKernel N hN t e q‖) :=
  integrable_moment_periodize _ m

theorem hasSum_mFourierCoeff_periodicKernel (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (hsmall : ‖realFrequency k + realFrequency p‖ ≤ N / 256) :
    HasSum (fun n : ℕ ↦ UnitAddTorus.mFourierCoeff
      (periodicKernel N hN (dyadicParameter n) e) (pairWavevector k p))
      ((Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
        pressurePairOperator e he k p) := by
  apply (hasSum_fourier_operatorKernel N hN e he k p hsmall).congr
  intro S
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [mFourierCoeff_periodicKernel _ _ _ _ he, fourier_operatorKernel _ _ _ _ he]

theorem moment_periodicKernel_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (m : ℕ) :
    (∫ q : T6, ‖q‖ ^ m * ‖periodicKernel N hN t e q‖) ≤
      ∫ x : E6, ‖x‖ ^ m * ‖operatorKernel N hN t e x‖ :=
  integral_moment_periodize_le _ m

theorem exists_uniform_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ q : T6, ‖periodicKernel N hN t e q‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_mass
  refine ⟨C, hC, ?_⟩
  intro N hN t ht e he
  have h := moment_periodicKernel_le N hN t e 0
  simp only [pow_zero, one_mul] at h
  exact h.trans (hb N hN t ht e he)

theorem exists_uniform_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ q : T6, ‖q‖ * ‖periodicKernel N hN t e q‖) ≤ (ratio t / N) * C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_firstMoment
  refine ⟨C, hC, ?_⟩
  intro N hN t ht e he
  have h := moment_periodicKernel_le N hN t e 1
  simp only [pow_one] at h
  exact h.trans (hb N hN t ht e he)

theorem exists_uniform_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n ↦ ∫ q : T6, ‖periodicKernel N hN (dyadicParameter n) e q‖) ∧
      (∑' n, ∫ q : T6, ‖periodicKernel N hN (dyadicParameter n) e q‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_mass_budget
  refine ⟨C, hC, ?_⟩
  intro N hN e he
  obtain ⟨hsum, hbound⟩ := hb N hN e he
  have hle (n : ℕ) : (∫ q : T6, ‖periodicKernel N hN (dyadicParameter n) e q‖) ≤
      ∫ x : E6, ‖operatorKernel N hN (dyadicParameter n) e x‖ := by
    simpa only [pow_zero, one_mul] using moment_periodicKernel_le N hN (dyadicParameter n) e 0
  have hs := Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun q ↦ norm_nonneg _)) hle hsum
  exact ⟨hs, (hs.tsum_le_tsum hle hsum).trans hbound⟩

theorem exists_uniform_firstMoment_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n ↦ ∫ q : T6, ‖q‖ * ‖periodicKernel N hN (dyadicParameter n) e q‖) ∧
      (∑' n, ∫ q : T6, ‖q‖ * ‖periodicKernel N hN (dyadicParameter n) e q‖) ≤ C / N := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_firstMoment_budget
  refine ⟨C, hC, ?_⟩
  intro N hN e he
  obtain ⟨hsum, hbound⟩ := hb N hN e he
  have hle (n : ℕ) : (∫ q : T6, ‖q‖ * ‖periodicKernel N hN (dyadicParameter n) e q‖) ≤
      ∫ x : E6, ‖x‖ * ‖operatorKernel N hN (dyadicParameter n) e x‖ := by
    simpa only [pow_one] using moment_periodicKernel_le N hN (dyadicParameter n) e 1
  have hs := Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun q ↦ by positivity)) hle hsum
  exact ⟨hs, (hs.tsum_le_tsum hle hsum).trans hbound⟩

theorem exists_uniform_twoInputMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ q : T6, (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) *
        ‖periodicKernel N hN t e q‖) ≤ (ratio t / N) * C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_firstMoment
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro N hN t ht e he
  apply (integral_twoInputMoment_periodize_le (operatorKernel N hN t e)).trans
  exact (mul_le_mul_of_nonneg_left (hb N hN t ht e he) (by norm_num)).trans_eq (by ring)

theorem exists_uniform_twoInputMoment_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n ↦ ∫ q : T6, (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) *
        ‖periodicKernel N hN (dyadicParameter n) e q‖) ∧
      (∑' n, ∫ q : T6, (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) *
        ‖periodicKernel N hN (dyadicParameter n) e q‖) ≤ C / N := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicOperatorKernel.exists_uniform_firstMoment_budget
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro N hN e he
  obtain ⟨hsum, hbound⟩ := hb N hN e he
  have hle (n : ℕ) := integral_twoInputMoment_periodize_le (operatorKernel N hN (dyadicParameter n) e)
  have hs2 := hsum.mul_left 2
  have hs := Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun q ↦ by positivity)) hle hs2
  refine ⟨hs, ?_⟩
  have h := hs.tsum_le_tsum hle hs2
  rw [tsum_mul_left] at h
  exact (h.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization
