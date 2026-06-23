import Mettapedia.Computability.PNP.CruxKpolySampleMajorityFullFallback

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: base bounded-sample majority and fallback checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_surjective_iff_regression
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_surjective_iff
      Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_false_support_card_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_falseSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) sample

theorem kpoly_anchor_bounded_sample_majority_not_realizes_large_false_support_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_realizes_rule_of_sampleBound_lt_falseSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

theorem kpoly_anchor_bounded_sample_majority_default_nondefault_support_card_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_nondefaultSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) default sample

theorem kpoly_anchor_bounded_sample_majority_default_not_realizes_large_nondefault_support_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

theorem kpoly_anchor_bounded_sample_majority_default_surjective_iff_regression
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithDefault_surjective_iff
      default Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_fallback_empty_sample_regression
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

theorem kpoly_anchor_bounded_sample_majority_fallback_surjective_regression
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_surjective
      Z k sampleBound

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_cover_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_index_representative_cover_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_finite_predictor_quotient_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_finitePredictorQuotient_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_exact_visible_compression_regression
    {Z : Type v} [Fintype Z] {k s sampleBound : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_exactVisibleCompressionTarget_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_clocked_realization_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedRealization_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

theorem kpoly_anchor_bounded_sample_majority_fallback_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallback_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
