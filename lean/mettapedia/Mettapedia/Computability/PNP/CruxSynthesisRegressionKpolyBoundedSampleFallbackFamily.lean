import Mettapedia.Computability.PNP.CruxKpolySampleMajorityFallbackFamilyRadiusCover

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: fallback-family bounded-sample cover checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_fallback_family_disagreement_support_card_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

theorem kpoly_anchor_bounded_sample_majority_fallback_family_empty_sample_regression
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_of_fallback_surjective_regression
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_fallback_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_surjective_iff_fallback_surjective_regression
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_surjective_iff_fallback_surjective
      (Z := Z) (k := k) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_cover_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_index_representative_cover_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_finite_predictor_quotient_regression
    {FallbackIndex : Type v} {Z : Type v} {k N : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k 0 fallback).predictorFamily.FinitePredictorQuotient N ↔
      (FallbackZeroSampleImage.fallbackFamily fallback).FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_exact_visible_compression_regression
    {FallbackIndex : Type v} {Z : Type v} {k s : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackZeroSampleImage.ZeroSampleIndex FallbackIndex Z k)
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := FallbackIndex)
        (FallbackZeroSampleImage.fallbackFamily fallback) s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_clocked_realization_regression
    {FallbackIndex : Type v} {Z : Type v} {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (FallbackZeroSampleImage.fallbackFamily fallback).RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_zero_sample_clocked_payload_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (FallbackZeroSampleImage.fallbackFamily fallback) s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_zeroSample_clockedPayload_iff_fallbackFamily
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_not_realizes_large_disagreement_support_regression
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
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

theorem kpoly_anchor_bounded_sample_majority_fallback_family_finite_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_finitePredictorCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_exact_radius_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_iff_radius_cover_univ_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_surjective_iff_pointwise_radius_cover_regression
    {FallbackIndex : Type v} {Z : Type v} [Fintype FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_family_not_surjective_small_hamming_cover_regression
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
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_fallback_family_hamming_cover_product_lower_bound_regression
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
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

end Mettapedia.Computability.PNP.CruxSynthesisRegression
