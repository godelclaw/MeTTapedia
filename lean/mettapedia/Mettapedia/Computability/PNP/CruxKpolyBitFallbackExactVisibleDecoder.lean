import Mettapedia.Computability.PNP.CruxKpolyBitFallbackZeroSampleEquivalences

/-!
# PNP `Kpoly` bit-fallback exact-visible decoder anchors

This module contains the canonical exact-visible truth-table decoder wrappers
for arbitrary sample bounds and the resulting clocked-payload obstruction.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: the canonical full truth-table fallback decoder is
full-rule expressive for every sample bound; the empty sample is enough. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    (Z := Z) (k := k) (sampleBound := sampleBound)

/-- Route-coverage anchor: the raw exact-visible truth-table decoder itself is
surjective onto the full exact-visible rule family.  This is the compatibility
lemma needed to transport generic fallback-decoder theorems to the canonical
decoder specialization without re-proving them at the wrapper level. -/
theorem kpolyCoverage_anchor_exactVisibleRuleDecode_surjective
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective (exactVisibleRuleDecode (Z := Z) (k := k)) := by
  intro rule
  refine ⟨exactVisibleRuleEncode (Z := Z) (k := k) rule, ?_⟩
  simpa using exactVisibleRuleDecode_encode (Z := Z) (k := k) rule

/-- Route-coverage anchor: for the canonical exact-visible truth-table
fallback decoder, bounded sample-level plug-in majority already admits no
clocked finite-learning payload below the full exact-visible surface
threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_clockedPayload_of_exactVisibleRuleDecode_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)
      (clock := clock) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
        (Z := Z) (k := k) (sampleBound := sampleBound))

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already admits no clocked finite-learning payload
below the truth-table bit budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  simpa using
    (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_clockedPayload_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := 0) (s := s) (clock := clock) hs)
end Mettapedia.Computability.PNP
