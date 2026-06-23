import Mettapedia.Computability.PNP.CruxKpolyBitFallbackRadiusCover
import Mettapedia.Computability.PNP.CruxKpolySampleMajorityFallbackFamilyRadiusCover

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: bit-fallback family cover and initial bit-budget checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_exact_radius_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈
        PluginSampleMajority.fallbackFamilyRadiusCover
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
          sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback rule

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_finite_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.FinitePredictorCover
      (2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_finitePredictorCover
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_surjective_iff_radius_cover_univ_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
          sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_surjective_iff_pointwise_radius_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : BitCode fallbackBits,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_not_surjective_small_hamming_cover_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_binomial_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_binomial_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sum_choose_total_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sum_choose_total_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_fallback_bits_sample_bound_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_fallback_family_full_radius_surjective_regression
    {FallbackIndex : Type v} {Z : Type v}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithFallbackFamily_surjective_of_nonempty_of_surfaceCard_le_sampleBound
      (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
      (sampleBound := sampleBound) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_full_radius_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_of_surfaceCard_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hbound

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_fallback_bits_exact_boundary_regression
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback

end Mettapedia.Computability.PNP.CruxSynthesisRegression
