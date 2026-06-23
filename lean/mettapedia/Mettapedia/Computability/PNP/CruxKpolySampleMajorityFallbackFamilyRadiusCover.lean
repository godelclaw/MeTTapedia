import Mettapedia.Computability.PNP.CruxKpolySampleMajorityFallbackFamilyZeroSample

/-!
# PNP `Kpoly` sample-majority anchors: fallback-family radius covers

Radius-cover and product-budget anchors for structured fallback families with bounded sampled overrides.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a structured fallback family plus bounded samples
cannot realize a rule that is farther than `sampleBound` from every fallback
code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

/-- Route-coverage anchor: structured fallback plus bounded samples realizes
exactly the finite Hamming-radius cover around the fallback codes. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

/-- Route-coverage anchor: structured fallback plus bounded samples is
surjective exactly when the fallback-code Hamming cover is the full rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: the exact pointwise repair condition for structured
fallback plus bounded samples is radius-`sampleBound` coverage of every
exact-visible rule by some fallback code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, any nonempty structured fallback family is full-rule expressive.
Thus the bounded-sample obstruction is sharp at full radius. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
    (sampleBound := sampleBound) fallback hbound

/-- Route-coverage anchor: a structured fallback family plus bounded samples
has a predictor-image cover bounded by fallback-code count times the number of
small sparse override supports. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_finitePredictorCover
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

/-- Route-coverage anchor: if that Hamming-cover product is below the full
truth-table space, the structured fallback-family endpoint is not full-rule
expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

/-- Route-coverage anchor: full-rule expressivity of a structured fallback
family plus bounded samples forces the Hamming-cover product to reach the full
exact-visible Boolean truth-table count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj


end Mettapedia.Computability.PNP
