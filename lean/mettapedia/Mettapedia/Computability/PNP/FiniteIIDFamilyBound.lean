import Mettapedia.Computability.PNP.FiniteIIDAgreement

/-!
# Finite-family agreement bounds

The shared union bound controls samples consistent with an incorrect decoded
predictor. Code-indexed bounds retain the authored encoding; bounds over
realized predictors account for each distinct function once.
-/

namespace Mettapedia.Computability.PNP.EncodedFamily

open scoped ENNReal BigOperators
open Mettapedia.ProbabilityTheory

universe u v w

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

instance instDecidableAgreesWithTarget
    (target predict : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (AgreesWithTarget target predict sample) :=
  inferInstanceAs (Decidable (∀ i, predict (sample i) = target (sample i)))

instance instDecidableIsDeceptiveSample
    (target : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    Decidable (H.IsDeceptiveSample target sample) :=
  inferInstanceAs (Decidable (∃ c : H.Code, H.decode c ≠ target ∧
    AgreesWithTarget target (H.decode c) sample))

variable (μ : PMF Input) (target : Input → Output) (m : Nat)

/-- The total `μ^m`-mass of deceptive samples for `target`. -/
noncomputable def deceptiveSampleMass : ℝ≥0∞ :=
  ∑ sample : H.DeceptiveSamples target m, sampleMass μ sample.1

/-- The weighted deceptive mass as a full sample-space sum with an indicator. -/
theorem deceptiveSampleMass_eq_sum_indicator :
    H.deceptiveSampleMass μ target m =
      ∑ sample : PointSample Input m,
        if H.IsDeceptiveSample target sample then sampleMass μ sample else 0 := by
  classical
  simpa [FiniteEventMass.mass, deceptiveSampleMass, DeceptiveSamples] using
    (FiniteEventMass.mass_subtype (sampleMass μ) (H.IsDeceptiveSample target)).symm

/-- The weighted deceptive mass is bounded by the sum of the weighted consistent
sample masses of the bad codes. -/
theorem deceptiveSampleMass_le_badCodeConsistentMassSum :
    H.deceptiveSampleMass μ target m ≤
      ∑ c : H.BadCodes target, consistentSampleMass μ target (H.decode c.1) m := by
  classical
  have bound := FiniteEventMass.union_le (fun sample : PointSample Input m => sampleMass μ sample)
    (fun _ => bot_le) (fun (c : H.BadCodes target) sample =>
      decide (AgreesWithTarget target (H.decode c.1) sample))
  simp [FiniteEventMass.mass_subtype, BadCodes, IsDeceptiveSample,
    ConsistentSamples, DeceptiveSamples, deceptiveSampleMass, consistentSampleMass] at bound ⊢
  convert! bound using 1; congr!
  all_goals exact congrArg (@Fintype.elems _) (Subsingleton.elim _ _)

/-- The weighted deceptive mass is bounded by the sum of the bad-code
one-step agreement masses raised to the sample length. -/
theorem deceptiveSampleMass_le_badCodeAgreementMassSum :
    H.deceptiveSampleMass μ target m ≤
      ∑ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ^ m := by
  simpa only [consistentSampleMass_eq_agreementMass_pow] using
    H.deceptiveSampleMass_le_badCodeConsistentMassSum μ target m

/-- Uniform weighted union bound: if every bad code has one-step agreement mass
at most `q`, then the total deceptive mass is at most `|Code(H)| * q^m`. -/
theorem deceptiveSampleMass_le_codeCard_mul_pow_of_agreementMass_le {q : ℝ≥0∞}
    (hq : ∀ c : H.BadCodes target, agreementMass μ target (H.decode c.1) ≤ q) :
    H.deceptiveSampleMass μ target m ≤ (Fintype.card H.Code : ℝ≥0∞) * q ^ m := by
  refine (H.deceptiveSampleMass_le_badCodeAgreementMassSum μ target m).trans ?_
  calc
    _ ≤ ∑ _c : H.BadCodes target, q ^ m :=
      Finset.sum_le_sum fun c _ => (pow_left_mono m) (hq c)
    _ = (Fintype.card (H.BadCodes target) : ℝ≥0∞) * q ^ m := by simp
    _ ≤ (Fintype.card H.Code : ℝ≥0∞) * q ^ m := by
      gcongr
      exact_mod_cast Fintype.card_subtype_le (fun c : H.Code => H.decode c ≠ target)

/-- Distinct incorrect predictions, independent of how many codes denote each one. -/
abbrev BadPredictors (target : Input → Output) := {h : H.realized // h.1 ≠ target}

noncomputable instance badPredictorsFintype (target : Input → Output) :
    Fintype (H.BadPredictors target) := Fintype.ofFinite _

omit [Fintype Input] [DecidableEq Output] in
theorem card_badPredictors_le_badCodes :
    Fintype.card (H.BadPredictors target) ≤ Fintype.card (H.BadCodes target) := by
  apply Fintype.card_le_of_surjective (fun c : H.BadCodes target =>
    (⟨⟨H.decode c.1, ⟨c.1, rfl⟩⟩, c.2⟩ : H.BadPredictors target))
  rintro ⟨⟨_, ⟨c, rfl⟩⟩, bad⟩
  exact ⟨⟨c, bad⟩, rfl⟩

omit [Fintype Input] [DecidableEq Output] in
theorem isDeceptiveSample_iff_realized (target : Input → Output) {m : Nat} (sample : PointSample Input m) :
    H.IsDeceptiveSample target sample ↔
      ∃ h ∈ H.realized, h ≠ target ∧ AgreesWithTarget target h sample := by
  constructor
  · rintro ⟨c, bad, agrees⟩; exact ⟨H.decode c, ⟨c, rfl⟩, bad, agrees⟩
  · rintro ⟨_, ⟨c, rfl⟩, bad, agrees⟩; exact ⟨c, bad, agrees⟩

theorem deceptiveSampleMass_eq_of_realized_eq (K : EncodedFamily Input Output)
    (same : H.realized = K.realized) (μ : PMF Input) (target : Input → Output) (m : Nat) :
    H.deceptiveSampleMass μ target m = K.deceptiveSampleMass μ target m := by
  rw [H.deceptiveSampleMass_eq_sum_indicator, K.deceptiveSampleMass_eq_sum_indicator]
  exact Finset.sum_congr rfl fun sample _ => if_congr
    (by rw [H.isDeceptiveSample_iff_realized, K.isDeceptiveSample_iff_realized, same]) rfl rfl

/-- The union bound over predictions avoids overcounting duplicate encodings. -/
theorem deceptiveSampleMass_le_badPredictorAgreementMassSum :
    H.deceptiveSampleMass μ target m ≤
      ∑ h : H.BadPredictors target, agreementMass μ target h.1.1 ^ m := by
  classical
  have bound := FiniteEventMass.union_le (fun sample : PointSample Input m => sampleMass μ sample)
    (fun _ => bot_le) (fun (h : H.BadPredictors target) sample =>
      decide (AgreesWithTarget target h.1.1 sample))
  simp_rw [← consistentSampleMass_eq_agreementMass_pow]
  simp [FiniteEventMass.mass_subtype, BadPredictors, realized, IsDeceptiveSample,
    ConsistentSamples, DeceptiveSamples, deceptiveSampleMass, consistentSampleMass] at bound ⊢
  convert! bound using 1; congr!
  all_goals exact congrArg (@Fintype.elems _) (Subsingleton.elim _ _)

theorem deceptiveSampleMass_le_badPredictorCard_mul_pow_of_agreementMass_le {q : ℝ≥0∞}
    (hq : ∀ h : H.BadPredictors target, agreementMass μ target h.1.1 ≤ q) :
    H.deceptiveSampleMass μ target m ≤ (Fintype.card (H.BadPredictors target) : ℝ≥0∞) * q ^ m := by
  refine (H.deceptiveSampleMass_le_badPredictorAgreementMassSum μ target m).trans ?_
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun h _ => (pow_left_mono m) (hq h))

end Mettapedia.Computability.PNP.EncodedFamily
