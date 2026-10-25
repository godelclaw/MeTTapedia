import Mettapedia.Computability.PNP.FiniteIIDFamilyBound
import Mettapedia.Computability.PNP.FiniteUniformRate

/-!
# Finite-sample recovery

Deceptive and nondeceptive events partition product sampling. Realizability
makes every nondeceptive sample yield exact ERM recovery. The lower bounds
reuse code and distinct-predictor union estimates while retaining the chosen
minimizer; coding invariance concerns the failure event, not that choice.
-/

namespace Mettapedia.Computability.PNP.EncodedFamily

open scoped ENNReal BigOperators
open Mettapedia.ProbabilityTheory

universe u v

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- The total `μ^m`-mass of nondeceptive samples. -/
noncomputable def nondeceptiveSampleMass
    (μ : PMF Input) (target : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : H.NondeceptiveSamples target m, sampleMass μ sample.1

/-- The total `μ^m`-mass of exact ERM recovery samples. -/
noncomputable def exactRecoverySampleMass
    [Nonempty H.Code]
    (μ : PMF Input) (target : Input → Output) (m : ℕ) : ℝ≥0∞ :=
  ∑ sample : H.ExactRecoverySamples target m, sampleMass μ sample.1

noncomputable instance instDecidableExactRecoverySample
    [Nonempty H.Code]
    (target : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (H.empiricalRiskPredictor (labeledByTarget target sample) = target) := by
  classical
  infer_instance

variable [Nonempty H.Code] (μ : PMF Input) (target : Input → Output) (m : Nat)

omit [Nonempty H.Code] in
theorem nondeceptiveSampleMass_eq_sum_indicator :
    H.nondeceptiveSampleMass μ target m =
      ∑ sample : PointSample Input m,
        if ¬ H.IsDeceptiveSample target sample then sampleMass μ sample else 0 := by
  simpa [FiniteEventMass.mass, nondeceptiveSampleMass, NondeceptiveSamples] using
    (FiniteEventMass.mass_subtype (sampleMass μ) (fun sample : PointSample Input m => ¬ H.IsDeceptiveSample target sample)).symm

theorem exactRecoverySampleMass_eq_sum_indicator :
    H.exactRecoverySampleMass μ target m =
      ∑ sample : PointSample Input m,
        if H.empiricalRiskPredictor (labeledByTarget target sample) = target then
          sampleMass μ sample
        else 0 := by
  simpa [FiniteEventMass.mass, exactRecoverySampleMass, ExactRecoverySamples] using
    (FiniteEventMass.mass_subtype (sampleMass μ) (fun sample : PointSample Input m => H.empiricalRiskPredictor (labeledByTarget target sample) = target)).symm

theorem sampleMass_sum_eq_one :
    (∑ sample : PointSample Input m, sampleMass μ sample) = 1 := by
  change (∑ sample : Fin m → Input, ∏ i, μ (sample i)) = 1
  rw [← Fintype.sum_pow]
  have total : (∑ x, μ x) = 1 := by simpa [tsum_fintype] using μ.tsum_coe
  simp only [total, one_pow]

omit [Nonempty H.Code] in
theorem nondeceptiveSampleMass_add_deceptiveSampleMass :
    H.nondeceptiveSampleMass μ target m + H.deceptiveSampleMass μ target m = 1 := by
  rw [add_comm]
  unfold nondeceptiveSampleMass deceptiveSampleMass
  have partition := (Fintype.sum_subtype_add_sum_subtype (H.IsDeceptiveSample target)
    (sampleMass μ)).trans (sampleMass_sum_eq_one μ m)
  convert! partition using 1; congr!

omit [Nonempty H.Code] in
theorem one_sub_deceptiveSampleMass_le_nondeceptiveSampleMass :
    1 - H.deceptiveSampleMass μ target m ≤ H.nondeceptiveSampleMass μ target m := by
  apply tsub_le_iff_right.2
  simpa [add_comm] using
    (le_of_eq (H.nondeceptiveSampleMass_add_deceptiveSampleMass μ target m).symm)

theorem exactRecoverySampleMass_ge_nondeceptiveSampleMass
    (htarget : ∃ c : H.Code, H.decode c = target) :
    H.nondeceptiveSampleMass μ target m ≤ H.exactRecoverySampleMass μ target m := by
  classical
  have bound := FiniteEventMass.mono (fun sample : PointSample Input m => sampleMass μ sample)
      (fun _ => bot_le)
      (first := fun sample => decide (¬ H.IsDeceptiveSample target sample))
      (second := fun sample => decide (H.empiricalRiskPredictor (labeledByTarget target sample) = target))
      (fun sample accepted => decide_eq_true
        (H.empiricalRiskPredictor_eq_target_of_not_deceptive target sample htarget (of_decide_eq_true accepted)))
  simp only [FiniteEventMass.mass_subtype] at bound
  unfold nondeceptiveSampleMass exactRecoverySampleMass
  convert! bound using 1

theorem exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - H.deceptiveSampleMass μ target m ≤ H.exactRecoverySampleMass μ target m := by
  exact le_trans
    (H.one_sub_deceptiveSampleMass_le_nondeceptiveSampleMass μ target m)
    (H.exactRecoverySampleMass_ge_nondeceptiveSampleMass μ target m htarget)

theorem exactRecoverySampleMass_ge_one_sub_badCodeAgreementMassSum
    (htarget : ∃ c : H.Code, H.decode c = target) :
    1 - ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m ≤
      H.exactRecoverySampleMass μ target m := by
  exact (tsub_le_tsub_left (H.deceptiveSampleMass_le_badCodeAgreementMassSum μ target m) 1).trans
    (H.exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass μ target m htarget)

theorem exactRecoverySampleMass_ge_one_sub_codeCard_mul_pow_of_agreementMass_le
    (htarget : ∃ c : H.Code, H.decode c = target)
    {q : ℝ≥0∞}
    (hq : ∀ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ≤ q) :
    1 - (Fintype.card H.Code : ℝ≥0∞) * q ^ m ≤
      H.exactRecoverySampleMass μ target m := by
  exact (tsub_le_tsub_left (H.deceptiveSampleMass_le_codeCard_mul_pow_of_agreementMass_le μ target m hq) 1).trans
    (H.exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass μ target m htarget)

/-- Exact recovery inherits the bound over distinct incorrect predictions. -/
theorem exactRecoverySampleMass_ge_one_sub_badPredictorCard_mul_pow_of_agreementMass_le
    (htarget : ∃ c : H.Code, H.decode c = target) {q : ℝ≥0∞}
    (hq : ∀ h : H.BadPredictors target, agreementMass μ target h.1.1 ≤ q) :
    1 - (Fintype.card (H.BadPredictors target) : ℝ≥0∞) * q ^ m ≤ H.exactRecoverySampleMass μ target m :=
  (tsub_le_tsub_left (H.deceptiveSampleMass_le_badPredictorCard_mul_pow_of_agreementMass_le μ target m hq) 1).trans
    (H.exactRecoverySampleMass_ge_one_sub_deceptiveSampleMass μ target m htarget)

end Mettapedia.Computability.PNP.EncodedFamily
