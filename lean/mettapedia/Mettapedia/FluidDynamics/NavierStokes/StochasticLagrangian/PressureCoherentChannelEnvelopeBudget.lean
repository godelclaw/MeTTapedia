import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceTruncatedBudget

/-!
# Summable common envelopes for all coherent pressure channels

The matched input and output bands share direction-independent envelopes.
A single full-measure set works for every band, direction, and channel.
The envelope masses and wrapped first moments are summable over both
indices. The first-moment budget carries an explicit logarithmic loss.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelEnvelopeBudget

open MeasureTheory Mettapedia.Analysis.GeometricMinSeries
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentChannelPeriodization
open PressureLowOutputDyadicBudget (dyadicParameter dyadicParameter_mem)
open PressureFixedOutputSymbol
open PressureCoherentDivergenceTruncatedBudget (inv_inputScale logarithmicCost)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
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

def matchedPeriodicKernel (N : ℝ) (hN : 0 < N) (j m : ℕ) (e : R3) (c : Factor) : T6 → Op :=
  periodicKernel (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m)) e c

theorem exists_uniform_matched_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℕ → ℕ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N,
        (∀ j m, (∀ q, 0 ≤ M N hN j m q) ∧ Measurable (M N hN j m) ∧
          Integrable (M N hN j m) ∧ Integrable (fun q ↦ ‖q‖ * M N hN j m q) ∧
          (∫ q : T6, M N hN j m q) ≤ (C / 256) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ m ∧
          (∫ q : T6, ‖q‖ * M N hN j m q) ≤
            C * (1 / 2 : ℝ) ^ j * min ((1 / 512 : ℝ) * (1 / 2 : ℝ) ^ m) N⁻¹) ∧
        (∀ᵐ q : T6, ∀ j m : ℕ, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖matchedPeriodicKernel N hN j m e c q‖ ≤ M N hN j m q) := by
  obtain ⟨C, hC, H, hb⟩ := exists_uniform_periodic_envelope
  refine ⟨C, hC, fun N hN j m ↦
    H (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m)), ?_⟩
  intro N hN
  have h (j m : ℕ) := hb (inputScale N j) (inputScale_pos N hN j)
    _ (dyadicParameter_mem (j + m))
  constructor
  · intro j m
    obtain ⟨hn, hm, hi, hfirst, _, hmass, hmom⟩ := h j m
    refine ⟨hn, hm, hi, hfirst, hmass.trans_eq ?_, ?_⟩
    · rw [ratio_matched]; ring
    · rw [ratio_matched, inv_inputScale] at hmom
      have heq : ((1 / 256 : ℝ) * (1 / 2) ^ j * (1 / 2) ^ m) / 2 =
          (1 / 2 : ℝ) ^ j * ((1 / 512 : ℝ) * (1 / 2) ^ m) := by ring
      rw [heq, ← mul_min_of_nonneg _ _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)] at hmom
      exact hmom.trans_eq (by ring)
  · exact ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (fun m ↦ (h j m).2.2.2.2.1))

theorem exists_uniform_matched_envelope_budget :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℕ → ℕ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N,
        (∀ j m, (∀ q, 0 ≤ M N hN j m q) ∧ Measurable (M N hN j m) ∧
          Integrable (M N hN j m) ∧ Integrable (fun q ↦ ‖q‖ * M N hN j m q)) ∧
        (∀ᵐ q : T6, ∀ j m : ℕ, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖matchedPeriodicKernel N hN j m e c q‖ ≤ M N hN j m q) ∧
        ∀ J : ℕ,
          ((∀ j, Summable (fun m ↦ ∫ q : T6, M N hN (J + j) m q)) ∧
            Summable (fun j ↦ ∑' m, ∫ q : T6, M N hN (J + j) m q) ∧
            (∑' j, ∑' m, ∫ q : T6, M N hN (J + j) m q) ≤ C0 * (1 / 2 : ℝ) ^ J) ∧
          ((∀ j, Summable (fun m ↦ ∫ q : T6, ‖q‖ * M N hN (J + j) m q)) ∧
            Summable (fun j ↦ ∑' m, ∫ q : T6, ‖q‖ * M N hN (J + j) m q) ∧
            (∑' j, ∑' m, ∫ q : T6, ‖q‖ * M N hN (J + j) m q) ≤
              C1 * (1 / 2 : ℝ) ^ J / N * logarithmicCost N (1 / 2)) := by
  obtain ⟨C, hC, M, hb⟩ := exists_uniform_matched_envelope
  refine ⟨C / 64, 2 * C, div_nonneg hC (by norm_num), mul_nonneg (by norm_num) hC, M, ?_⟩
  intro N hN
  obtain ⟨h, hae⟩ := hb N hN
  refine ⟨fun j m ↦ ⟨(h j m).1, (h j m).2.1, (h j m).2.2.1, (h j m).2.2.2.1⟩, hae, ?_⟩
  intro J
  constructor
  · have hout (j : ℕ) :
        Summable (fun m ↦ ∫ q : T6, M N hN (J + j) m q) ∧
        (∑' m, ∫ q : T6, M N hN (J + j) m q) ≤ C / 128 * (1 / 2 : ℝ) ^ (J + j) := by
      have hs := hasSum_geometric_two.mul_left (C / 256 * (1 / 2 : ℝ) ^ (J + j))
      have hle (m : ℕ) := (h (J + j) m).2.2.2.2.1
      have hi := Summable.of_nonneg_of_le
        (fun m ↦ integral_nonneg (h (J + j) m).1) hle hs.summable
      refine ⟨hi, ?_⟩
      have ht := hi.tsum_le_tsum hle hs.summable
      rw [hs.tsum_eq] at ht
      exact ht.trans_eq (by ring)
    have hs := hasSum_geometric_two.mul_left (C / 128 * (1 / 2 : ℝ) ^ J)
    have hj (j : ℕ) : (∑' m, ∫ q : T6, M N hN (J + j) m q) ≤
        (C / 128 * (1 / 2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ j :=
      (hout j).2.trans_eq (by rw [pow_add]; ring)
    have ho := Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg (fun m ↦ integral_nonneg (h (J + j) m).1)) hj hs.summable
    refine ⟨fun j ↦ (hout j).1, ho, ?_⟩
    have ht := ho.tsum_le_tsum hj hs.summable
    rw [hs.tsum_eq] at ht
    exact ht.trans_eq (by ring)
  · have hle (j m : ℕ) : (∫ q : T6, ‖q‖ * M N hN (J + j) m q) ≤
        (C * (1 / 2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ j *
          min ((1 / 512 : ℝ) * (1 / 2 : ℝ) ^ m) N⁻¹ :=
      (h (J + j) m).2.2.2.2.2.trans_eq (by rw [pow_add]; ring)
    obtain ⟨hi, ho, ht⟩ := iterated_tsum_le_logarithmic_of_nonneg_of_le
      (mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J))
      (by norm_num : (0 : ℝ) ≤ 1 / 512) (inv_nonneg.mpr hN.le)
      (fun j m ↦ integral_nonneg (fun q ↦ mul_nonneg (norm_nonneg _) ((h (J + j) m).1 q))) hle
    refine ⟨hi, ho, ht.trans_eq ?_⟩
    have heq : (1 / 512 : ℝ) / N⁻¹ = (1 / 2 : ℝ) * N / 256 := by
      rw [div_eq_mul_inv, inv_inv]; ring
    rw [heq]
    unfold logarithmicCost
    ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelEnvelopeBudget
