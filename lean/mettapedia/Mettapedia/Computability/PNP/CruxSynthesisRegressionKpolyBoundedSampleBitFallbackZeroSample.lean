import Mettapedia.Computability.PNP.CruxKpolyBitFallbackExactVisibleDecoder

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: bit-fallback zero-sample and exact-decoder cover checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_surjective_regression
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
      (Z := Z) (k := k)

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_predictor_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_index_representative_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_finite_predictor_quotient_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorQuotient_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_exact_visible_compression_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex
          Z k (Fintype.card (ExactVisiblePostSwitchSurface Z k)))
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exactVisibleCompressionTarget_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_clocked_exact_visible_realization_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exists_clockedExactVisibleRealization_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_surjective_iff_fallback_surjective_regression
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_surjective_iff_fallback_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_predictor_cover_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_index_representative_cover_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FiniteIndexRepresentativeCover N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finiteIndexRepresentativeCover_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_finite_predictor_quotient_regression
    {Z : Type v} {k fallbackBits N : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.FinitePredictorQuotient N ↔
      (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_finitePredictorQuotient_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (N := N) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_visible_compression_regression
    {Z : Type v} {k fallbackBits s : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex Z k fallbackBits)
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s ↔
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitCode fallbackBits)
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleCompressionTarget_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_clocked_exact_visible_realization_regression
    {Z : Type v} {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.RealizedByClockedBitFamily F) ↔
      ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback).RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exists_clockedExactVisibleRealization_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k fallbackBits s clock : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily s clock ↔
      ClockedKpolyFiniteLearningPayload
        (BitFallbackZeroSampleImage.fallbackDecoderFamily fallback) s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_clockedPayload_iff_fallbackDecoderFamily
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (s := s) (clock := clock) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_decoder_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_exactVisibleRuleDecode
      (Z := Z) (k := k) (sampleBound := sampleBound)

theorem kpoly_anchor_exact_visible_rule_decode_surjective_regression
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective (exactVisibleRuleDecode (Z := Z) (k := k)) := by
  exact kpolyCoverage_anchor_exactVisibleRuleDecode_surjective (Z := Z) (k := k)

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_decoder_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k sampleBound s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_clockedPayload_of_exactVisibleRuleDecode_of_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound) (s := s) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_exact_decoder_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
