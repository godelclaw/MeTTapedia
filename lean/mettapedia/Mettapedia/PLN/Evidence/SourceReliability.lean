import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.PLN.Evidence.EvidenceKind

/-!
# Source Reliability Model (Dawid-Skene Layer)

The MODEL (not the EM algorithm) for source-specific reliability:
each evidence source has an accuracy profile that determines how much
its contributions should be trusted.

## Design

This is EvidentialLedger Layer 2: the reliability layer that sits
ABOVE the additive evidence composition (Layer 1). It does NOT
replace additive aggregation — it ADJUSTS the contributions before
they enter the additive fold.

Key separation (Dawid & Skene 1979):
- Layer 1 (EvidentialLedger): aggregate → evidence
- Layer 2 (this file): reliability → adjusted evidence → aggregate

## What This File Does

1. Defines `ReliabilityProfile`: per-source accuracy (tp_rate, tn_rate)
2. Defines `reliabilityAdjust`: weight reports by the source's signed
   informativeness, reading an anti-informative source through the exchange of
   channels
3. Proves: perfect sources preserve, random sources contribute nothing, reliably
   inverted sources are swapped, the adjustment commutes with the exchange of
   channels, and monotonicity in the weight
4. Defines `defaultReliability`: EvidenceKind-dependent priors

## What This File Does NOT Do

- EM algorithm for learning reliability from data (future work)
- Confusion matrices or Rasch models (more complex reliability models)
- Integration with `WeightedSourceItem` (already have `weight : Nat`)

## References

- Dawid & Skene 1979: "ML Estimation of Observer Error-Rates Using EM"
- Youden 1950: "Index for rating diagnostic tests"
- O'Hagan 2019: expert elicitation with reliability priors
- Colson & Cooke 2018: classical model for expert validation

-/

namespace Mettapedia.PLN.Evidence.SourceReliability

open Mettapedia.PLN.Evidence

/-! ## 1. Reliability profile -/

/-- Per-source reliability profile.
    `tpRate` = P(source reports + | truth is +) (sensitivity)
    `tnRate` = P(source reports − | truth is −) (specificity)
    Both in [0, 1000] (× 1000 encoding for kernel-checkable arithmetic). -/
structure ReliabilityProfile where
  tpRate : Nat  -- true positive rate × 1000 (1000 = perfect)
  tnRate : Nat  -- true negative rate × 1000 (1000 = perfect)
  calibrationObs : Nat  -- number of calibration observations
  deriving DecidableEq, BEq, Repr

/-! ## 2. Named profiles -/

/-- Perfect reliability: source always reports correctly. -/
def perfectProfile : ReliabilityProfile := ⟨1000, 1000, 0⟩

/-- Uninformative profile: source reports at random. -/
def uninformativeProfile : ReliabilityProfile := ⟨500, 500, 0⟩

/-- Inverted profile: the source always reports the opposite. -/
def invertedProfile : ReliabilityProfile := ⟨0, 0, 0⟩

/-! ## 3. Reliability adjustment

A report is evidence through the source's confusion matrix.  A positive report
supports a positive truth exactly when it is more likely under a positive truth
than under a negative one, `tpRate > 1000 - tnRate`, and a negative report supports
a negative truth under the same condition.  Both kinds of report therefore carry
the same signed weight, the difference `tpRate + tnRate - 1000` (Youden's index):
positive for an informative source, zero for a source that reports at random, and
negative for a source that tends to report the opposite.  In the model of Dawid and
Skene the sign is exact, and the index is the first-order log-likelihood weight of a
report near a random source.

The adjustment scales the reports by the weight when it is positive, and reads them
through the exchange of channels when it is negative: a reliably inverted source is
fully informative once its reports are swapped, and a random one contributes
nothing.  The weight is stored as two natural numbers, its positive part `excess`
and its negative part `deficit`, at most one of which is nonzero. -/

/-- The positive part of the source's signed weight, in thousandths. -/
def ReliabilityProfile.excess (p : ReliabilityProfile) : Nat :=
  p.tpRate + p.tnRate - 1000

/-- The negative part of the source's signed weight, in thousandths. -/
def ReliabilityProfile.deficit (p : ReliabilityProfile) : Nat :=
  1000 - (p.tpRate + p.tnRate)

/-- Exchange the positive and negative channels of count evidence. -/
def swapChannels (e : BinEvNat) : BinEvNat := ⟨e.neg, e.pos⟩

/-- Adjust raw evidence by source reliability: the reports weighted by the positive
part of the signed weight, plus the exchanged reports weighted by its negative
part. -/
def reliabilityAdjust (p : ReliabilityProfile) (raw : BinEvNat) : BinEvNat :=
  ⟨(p.excess * raw.pos + p.deficit * raw.neg) / 1000,
    (p.excess * raw.neg + p.deficit * raw.pos) / 1000⟩

/-- Reading a source with its reports flipped: its positive reports become negative
ones and conversely, so its rates become the complements of the swapped ones. -/
def flipProfile (p : ReliabilityProfile) : ReliabilityProfile :=
  ⟨1000 - p.tpRate, 1000 - p.tnRate, p.calibrationObs⟩

/-! ## 4. Properties -/

/-- At most one part of the signed weight is nonzero. -/
theorem excess_eq_zero_or_deficit_eq_zero (p : ReliabilityProfile) :
    p.excess = 0 ∨ p.deficit = 0 := by
  unfold ReliabilityProfile.excess ReliabilityProfile.deficit
  omega

/-- **Sign of a positive report**: the weight is positive exactly when a positive
report is more likely under a positive truth than under a negative one. -/
theorem excess_pos_iff (p : ReliabilityProfile) (tnRange : p.tnRate ≤ 1000) :
    0 < p.excess ↔ 1000 - p.tnRate < p.tpRate := by
  unfold ReliabilityProfile.excess
  omega

/-- **Sign of a negative report**: the same condition, read from the negative side. -/
theorem excess_pos_iff_negative_report (p : ReliabilityProfile) (tpRange : p.tpRate ≤ 1000) :
    0 < p.excess ↔ 1000 - p.tpRate < p.tnRate := by
  unfold ReliabilityProfile.excess
  omega

/-- The weight is negative exactly when a positive report is less likely under a
positive truth than under a negative one. -/
theorem deficit_pos_iff (p : ReliabilityProfile) (tnRange : p.tnRate ≤ 1000) :
    0 < p.deficit ↔ p.tpRate < 1000 - p.tnRate := by
  unfold ReliabilityProfile.deficit
  omega

/-- Perfect reliability preserves raw evidence. -/
theorem perfect_preserves (raw : BinEvNat) :
    reliabilityAdjust perfectProfile raw = raw := by
  have excess : perfectProfile.excess = 1000 := rfl
  have deficit : perfectProfile.deficit = 0 := rfl
  ext
  · show (perfectProfile.excess * raw.pos + perfectProfile.deficit * raw.neg) / 1000 = raw.pos
    rw [excess, deficit, Nat.zero_mul, Nat.add_zero, Nat.mul_div_cancel_left _ (by decide)]
  · show (perfectProfile.excess * raw.neg + perfectProfile.deficit * raw.pos) / 1000 = raw.neg
    rw [excess, deficit, Nat.zero_mul, Nat.add_zero, Nat.mul_div_cancel_left _ (by decide)]

/-- **A reliably inverted source is read through the exchange of channels.** -/
theorem inverted_swaps (raw : BinEvNat) :
    reliabilityAdjust invertedProfile raw = swapChannels raw := by
  have excess : invertedProfile.excess = 0 := rfl
  have deficit : invertedProfile.deficit = 1000 := rfl
  ext
  · show (invertedProfile.excess * raw.pos + invertedProfile.deficit * raw.neg) / 1000 = raw.neg
    rw [excess, deficit, Nat.zero_mul, Nat.zero_add, Nat.mul_div_cancel_left _ (by decide)]
  · show (invertedProfile.excess * raw.neg + invertedProfile.deficit * raw.pos) / 1000 = raw.pos
    rw [excess, deficit, Nat.zero_mul, Nat.zero_add, Nat.mul_div_cancel_left _ (by decide)]

/-- **A source that reports at random contributes nothing.** -/
theorem adjust_eq_zero_of_random {p : ReliabilityProfile}
    (random : p.tpRate + p.tnRate = 1000) (raw : BinEvNat) :
    reliabilityAdjust p raw = ⟨0, 0⟩ := by
  have excess : p.excess = 0 := by unfold ReliabilityProfile.excess; omega
  have deficit : p.deficit = 0 := by unfold ReliabilityProfile.deficit; omega
  simp [reliabilityAdjust, excess, deficit]

theorem uninformative_zeroes (raw : BinEvNat) :
    reliabilityAdjust uninformativeProfile raw = ⟨0, 0⟩ :=
  adjust_eq_zero_of_random (by decide) raw

/-- **The adjustment commutes with the exchange of channels.** -/
theorem reliabilityAdjust_swapChannels (p : ReliabilityProfile) (raw : BinEvNat) :
    reliabilityAdjust p (swapChannels raw) = swapChannels (reliabilityAdjust p raw) :=
  rfl

/-- **A source and its flipped reading give the same evidence**: flipping the
profile is the same as exchanging the reports. -/
theorem reliabilityAdjust_flipProfile (p : ReliabilityProfile) (tpRange : p.tpRate ≤ 1000)
    (tnRange : p.tnRate ≤ 1000) (raw : BinEvNat) :
    reliabilityAdjust (flipProfile p) raw = reliabilityAdjust p (swapChannels raw) := by
  have excess : (flipProfile p).excess = p.deficit := by
    unfold flipProfile ReliabilityProfile.excess ReliabilityProfile.deficit
    simp only
    omega
  have deficit : (flipProfile p).deficit = p.excess := by
    unfold flipProfile ReliabilityProfile.excess ReliabilityProfile.deficit
    simp only
    omega
  ext
  · show ((flipProfile p).excess * raw.pos + (flipProfile p).deficit * raw.neg) / 1000 =
      (p.excess * raw.neg + p.deficit * raw.pos) / 1000
    rw [excess, deficit, Nat.add_comm]
  · show ((flipProfile p).excess * raw.neg + (flipProfile p).deficit * raw.pos) / 1000 =
      (p.excess * raw.pos + p.deficit * raw.neg) / 1000
    rw [excess, deficit, Nat.add_comm]

/-- A larger weight of either sign yields at least as much evidence in each
channel. -/
theorem reliabilityAdjust_mono {p₁ p₂ : ReliabilityProfile}
    (excess : p₁.excess ≤ p₂.excess) (deficit : p₁.deficit ≤ p₂.deficit) (raw : BinEvNat) :
    (reliabilityAdjust p₁ raw).pos ≤ (reliabilityAdjust p₂ raw).pos ∧
      (reliabilityAdjust p₁ raw).neg ≤ (reliabilityAdjust p₂ raw).neg := by
  constructor
  · exact Nat.div_le_div_right (Nat.add_le_add (Nat.mul_le_mul_right raw.pos excess)
      (Nat.mul_le_mul_right raw.neg deficit))
  · exact Nat.div_le_div_right (Nat.add_le_add (Nat.mul_le_mul_right raw.neg excess)
      (Nat.mul_le_mul_right raw.pos deficit))

/-- Among informative sources with the same specificity, a higher sensitivity
preserves at least as much evidence in each channel. -/
theorem tpRate_monotone_of_informative {p₁ p₂ : ReliabilityProfile}
    (sameTn : p₁.tnRate = p₂.tnRate) (informative : 1000 ≤ p₁.tpRate + p₁.tnRate)
    (higher : p₁.tpRate ≤ p₂.tpRate) (raw : BinEvNat) :
    (reliabilityAdjust p₁ raw).pos ≤ (reliabilityAdjust p₂ raw).pos ∧
      (reliabilityAdjust p₁ raw).neg ≤ (reliabilityAdjust p₂ raw).neg :=
  reliabilityAdjust_mono
    (by unfold ReliabilityProfile.excess; omega)
    (by unfold ReliabilityProfile.deficit; omega) raw

/-- Among informative sources with the same sensitivity, a higher specificity
preserves at least as much evidence in each channel. -/
theorem tnRate_monotone_of_informative {p₁ p₂ : ReliabilityProfile}
    (sameTp : p₁.tpRate = p₂.tpRate) (informative : 1000 ≤ p₁.tpRate + p₁.tnRate)
    (higher : p₁.tnRate ≤ p₂.tnRate) (raw : BinEvNat) :
    (reliabilityAdjust p₁ raw).pos ≤ (reliabilityAdjust p₂ raw).pos ∧
      (reliabilityAdjust p₁ raw).neg ≤ (reliabilityAdjust p₂ raw).neg :=
  reliabilityAdjust_mono
    (by unfold ReliabilityProfile.excess; omega)
    (by unfold ReliabilityProfile.deficit; omega) raw

/-! ### Controls -/

/-- Positive control: an asymmetric informative source, weight 700 thousandths. -/
theorem informative_example : reliabilityAdjust ⟨900, 800, 0⟩ ⟨10, 5⟩ = ⟨7, 3⟩ := by decide

/-- Positive control: an anti-informative source, weight minus 400 thousandths, read
through the exchange of channels. -/
theorem antiInformative_example : reliabilityAdjust ⟨300, 300, 0⟩ ⟨10, 5⟩ = ⟨2, 4⟩ := by
  decide

/-- Negative control: a reliably inverted source no longer loses its evidence. -/
theorem inverted_not_zeroed : reliabilityAdjust invertedProfile ⟨10, 5⟩ ≠ ⟨0, 0⟩ := by
  decide

/-- Negative control: below the random line a higher sensitivity is not more positive
evidence: the source's negative reports, read as positive, are trusted less. -/
theorem tpRate_not_monotone_when_antiInformative :
    (reliabilityAdjust ⟨200, 0, 0⟩ ⟨0, 10⟩).pos < (reliabilityAdjust ⟨0, 0, 0⟩ ⟨0, 10⟩).pos := by
  decide

/-! ## 5. EvidenceKind-dependent default reliability

Different epistemic kinds get different default reliability priors.
Empirical evidence (checkLang, data) gets high default reliability.
Expert-elicited gets moderate. Model-derived and text-interpreted
get lower defaults. -/

def defaultReliability : EvidenceKind → ReliabilityProfile
  | .empirical         => ⟨950, 950, 50⟩   -- high: data-backed
  | .expertElicited    => ⟨800, 800, 10⟩   -- moderate: structured judgment
  | .modelDerived      => ⟨700, 700, 5⟩    -- lower: model may be miscalibrated
  | .textInterpreted   => ⟨600, 600, 2⟩    -- low: human interpretation of text
  | .logicalDerivation => ⟨900, 900, 20⟩   -- high: formal entailment

/-- Empirical evidence has higher default reliability than text-interpreted. -/
theorem empirical_more_reliable_than_text :
    (defaultReliability .empirical).tpRate >
    (defaultReliability .textInterpreted).tpRate := by decide

/-- Logical derivation has higher reliability than model-derived. -/
theorem logical_more_reliable_than_model :
    (defaultReliability .logicalDerivation).tpRate >
    (defaultReliability .modelDerived).tpRate := by decide

/-! ## 6. Summary -/

theorem reliability_summary :
    -- Perfect preserves
    reliabilityAdjust perfectProfile ⟨10, 5⟩ = ⟨10, 5⟩ ∧
    -- Inverted is read through the exchange of channels
    reliabilityAdjust invertedProfile ⟨10, 5⟩ = ⟨5, 10⟩ ∧
    -- Random contributes nothing
    reliabilityAdjust uninformativeProfile ⟨10, 5⟩ = ⟨0, 0⟩ ∧
    -- Empirical > text-interpreted
    (defaultReliability .empirical).tpRate > (defaultReliability .textInterpreted).tpRate := by
  decide

#print axioms inverted_swaps
#print axioms uninformative_zeroes
#print axioms reliabilityAdjust_flipProfile
#print axioms reliability_summary

end Mettapedia.PLN.Evidence.SourceReliability
