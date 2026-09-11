import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPeriodization

/-!
# Common periodic pressure envelopes and summable dyadic costs

The majorant is chosen independently of the frozen direction. Its orbit
sum has one full-measure domination set for all directions, and a single
full-measure set suffices for all dyadic bands as well.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePeriodicEnvelope

open MeasureTheory FrequencyPairPeriodization FrequencyPairEnvelope
open PressureDyadicOperatorKernel PressureDyadicPeriodization PressureLowOutputDyadicBudget
open PressureLowOutputCutoff (ratio)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_uniform_periodic_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun q ↦ ‖q‖ * M N hN t q) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ‖periodicKernel N hN t e q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ (ratio t) ^ 2 * C0 ∧
        (∫ q : T6, ‖q‖ * M N hN t q) ≤ (ratio t / N) * C1 := by
  obtain ⟨C0, C1, hC0, hC1, H, hb⟩ := PressureDyadicEnvelope.exists_uniform_operator_envelope
  refine ⟨C0, C1, hC0, hC1, fun N hN t ↦ periodize (H N hN t), ?_⟩
  intro N hN t ht
  obtain ⟨hn, hc, hi, hm, hk, hmass, hmom⟩ := hb N hN t ht
  refine ⟨periodize_nonneg _ hn, measurable_periodize _ hc.measurable, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_zero, one_mul] using
      FrequencyPairEnvelope.integrable_moment_periodize _ hn hc.measurable 0 (by simpa using hi)
  · simpa only [pow_one] using
      FrequencyPairEnvelope.integrable_moment_periodize _ hn hc.measurable 1 (by simpa using hm)
  · have h := ae_norm_periodize_family_le
      (fun e : {e : R3 // ‖e‖ = 1} ↦ operatorKernel N hN t e.1)
      (H N hN t) hn hc.measurable hi (fun e x ↦ hk e.1 e.2 x)
    filter_upwards [h] with q hq e he
    exact hq ⟨e, he⟩
  · apply le_trans _ hmass
    simpa only [pow_zero, one_mul] using
      FrequencyPairEnvelope.integral_moment_periodize_le _ hn hc.measurable 0 (by simpa using hi)
  · apply le_trans _ hmom
    simpa only [pow_one] using
      FrequencyPairEnvelope.integral_moment_periodize_le _ hn hc.measurable 1 (by simpa using hm)

theorem exists_uniform_dyadic_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℕ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N,
        (∀ n, (∀ q, 0 ≤ M N hN n q) ∧ Measurable (M N hN n) ∧
          Integrable (M N hN n) ∧ Integrable (fun q ↦ ‖q‖ * M N hN n q)) ∧
        (∀ᵐ q : T6, ∀ n : ℕ, ∀ e : R3, ‖e‖ = 1 →
          ‖periodicKernel N hN (dyadicParameter n) e q‖ ≤ M N hN n q) ∧
        Summable (fun n ↦ ∫ q : T6, M N hN n q) ∧
        (∑' n, ∫ q : T6, M N hN n q) ≤ C0 ∧
        Summable (fun n ↦ ∫ q : T6, ‖q‖ * M N hN n q) ∧
        (∑' n, ∫ q : T6, ‖q‖ * M N hN n q) ≤ C1 / N := by
  obtain ⟨C0, C1, hC0, hC1, M, hb⟩ := exists_uniform_periodic_envelope
  refine ⟨C0 / 49152, C1 / 128, div_nonneg hC0 (by norm_num), div_nonneg hC1 (by norm_num),
    fun N hN n ↦ M N hN (dyadicParameter n), ?_⟩
  intro N hN
  have h (n : ℕ) := hb N hN _ (dyadicParameter_mem n)
  have hmass (n : ℕ) : (∫ q : T6, M N hN (dyadicParameter n) q) ≤
      (ratio (dyadicParameter n)) ^ 2 * C0 := (h n).2.2.2.2.2.1
  have hmom (n : ℕ) : (∫ q : T6, ‖q‖ * M N hN (dyadicParameter n) q) ≤
      ratio (dyadicParameter n) * (C1 / N) := ((h n).2.2.2.2.2.2).trans_eq (by ring)
  have hs0 := hasSum_ratio_sq.mul_right C0
  have hs1 := hasSum_ratio.mul_right (C1 / N)
  have hi0 := Summable.of_nonneg_of_le
    (fun n ↦ MeasureTheory.integral_nonneg (h n).1) hmass hs0.summable
  have hi1 := Summable.of_nonneg_of_le
    (fun n ↦ MeasureTheory.integral_nonneg (fun q ↦ mul_nonneg (norm_nonneg q) ((h n).1 q)))
    hmom hs1.summable
  refine ⟨fun n ↦ ⟨(h n).1, (h n).2.1, (h n).2.2.1, (h n).2.2.2.1⟩,
    ae_all_iff.mpr (fun n ↦ (h n).2.2.2.2.1), hi0, ?_, hi1, ?_⟩
  · have ht := hi0.tsum_le_tsum hmass hs0.summable
    rw [hs0.tsum_eq] at ht
    exact ht.trans_eq (by ring)
  · have ht := hi1.tsum_le_tsum hmom hs1.summable
    rw [hs1.tsum_eq] at ht
    exact ht.trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressurePeriodicEnvelope
