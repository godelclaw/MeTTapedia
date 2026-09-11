import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairTruncatedMoment

/-!
# Periodic coherent bilinear channels with a shared capped moment

One full-measure set supports the envelope inequality simultaneously for
all unit directions and all seven channels. The wrapped first moment
uses the smaller of the half-torus mass cost and the Euclidean moment.
The actual Fourier coefficients preserve every normalized input factor.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization

open MeasureTheory FrequencyPairPeriodization FrequencyPairEnvelope
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentDivergenceChannelKernel (scaledMultiplier)
open PressureCoherentDivergenceOperatorKernel
open PressureLowOutputCutoff (ratio)
open scoped SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor) : T6 → Op :=
  periodize (operatorKernel N hN t e c)

theorem measurable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor) :
    Measurable (periodicKernel N hN t e c) :=
  measurable_periodize _ (operatorKernel N hN t e c).continuous.measurable

theorem integrable_periodicKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor) :
    Integrable (periodicKernel N hN t e c) := integrable_periodize _

theorem mFourierCoeff_periodicKernel_factor (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (n : Fin 6 → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicKernel N hN t e c) n =
      (scaledMultiplier N c (PressureLowOutputSymbol.pairEquiv
        (PancakeBilinearPeriodization.euclideanFrequencyPairOfWavevector n)) : ℂ) •
        UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) n := by
  simp only [periodicKernel,
    mFourierCoeff_periodize _ (operatorKernel N hN t e c).continuous.measurable
      (operatorKernel N hN t e c).integrable,
    mFourierCoeff_periodize _ (operatorKernel N hN t e .undifferentiated).continuous.measurable
      (operatorKernel N hN t e .undifferentiated).integrable,
    ← SchwartzMap.fourier_coe]
  exact fourier_operatorKernel_factor N hN t e c _

theorem exists_uniform_periodic_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun q ↦ ‖q‖ * M N hN t q) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖periodicKernel N hN t e c q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ ratio t * C ∧
        (∫ q : T6, ‖q‖ * M N hN t q) ≤ C * min (ratio t / 2) N⁻¹ := by
  obtain ⟨C0, C1, hC0, hC1, H, hb⟩ := PressureCoherentDivergenceEnvelope.exists_uniform_operator_envelope
  let C := max C0 C1
  have hC : 0 ≤ C := hC0.trans (le_max_left _ _)
  refine ⟨C, hC, fun N hN t ↦ periodize (H N hN t), ?_⟩
  intro N hN t ht
  obtain ⟨hn, hc, hi, hm, hk, hmass, hmom⟩ := hb N hN t ht
  have hp := periodize_nonneg _ hn
  have hip : Integrable (periodize (H N hN t)) := by
    simpa only [pow_zero, one_mul] using
      FrequencyPairEnvelope.integrable_moment_periodize _ hn hc.measurable 0 (by simpa using hi)
  have him : Integrable (fun q : T6 ↦ ‖q‖ * periodize (H N hN t) q) := by
    simpa only [pow_one] using
      FrequencyPairEnvelope.integrable_moment_periodize _ hn hc.measurable 1 (by simpa using hm)
  have hmp : (∫ q : T6, periodize (H N hN t) q) ≤ ratio t * C := by
    have h := FrequencyPairEnvelope.integral_moment_periodize_le _ hn hc.measurable 0
      (by simpa using hi)
    simp only [pow_zero, one_mul] at h
    exact (h.trans hmass).trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (div_nonneg ht.1 (by norm_num)))
  refine ⟨hp, measurable_periodize _ hc.measurable, hip, him, ?_, hmp, ?_⟩
  · have h := ae_norm_periodize_family_le
      (fun a : {e : R3 // ‖e‖ = 1} × Factor ↦ operatorKernel N hN t a.1.1 a.2)
      (H N hN t) hn hc.measurable hi (fun a x ↦ hk a.1.1 a.1.2 a.2 x)
    filter_upwards [h] with q hq e he c
    exact hq (⟨e, he⟩, c)
  · rw [mul_min_of_nonneg _ _ hC]
    apply le_min
    · calc
        _ ≤ ∫ q : T6, (1 / 2 : ℝ) * periodize (H N hN t) q :=
          integral_mono him (hip.const_mul _) (fun q ↦
            mul_le_mul_of_nonneg_right (norm_frequencyPairTorus_le_half q) (hp q))
        _ = (1 / 2 : ℝ) * ∫ q : T6, periodize (H N hN t) q := integral_const_mul _ _
        _ ≤ (1 / 2 : ℝ) * (ratio t * C) := mul_le_mul_of_nonneg_left hmp (by norm_num)
        _ = _ := by ring
    · have h := FrequencyPairEnvelope.integral_moment_periodize_le _ hn hc.measurable 1
        (by simpa using hm)
      simp only [pow_one] at h
      exact ((h.trans hmom).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) hN.le)).trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization
