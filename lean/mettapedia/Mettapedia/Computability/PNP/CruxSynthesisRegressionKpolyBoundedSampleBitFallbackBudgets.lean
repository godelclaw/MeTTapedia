import Mettapedia.Computability.PNP.CruxKpolyBitFallbackPolynomialEnvelope
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackSampleEnvelopeAnchors
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackZeroSampleObstructions

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: bit-fallback asymptotic budget checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_polynomial_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_polynomial_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_total_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_total_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_factor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + radiusBits + baseBits * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_factor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound + 1 ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + radiusBits + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sample_bound_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_sample_bound_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_raw_factor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_raw_factor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits radiusBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hradius : sampleBound ≤ 2 ^ radiusBits)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
      fallback hradius hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_zero_sample_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_product_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_overhead_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + overheadBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_two_sample_quadratic_overhead_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits overheadBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (henvelope :
      1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2 ≤
        2 ^ overheadBits)
    (hbits :
      fallbackBits + overheadBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
      fallback henvelope hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_successor_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + baseBits := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_successor_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1 ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + baseBits <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hbits

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_raw_surface_bit_lower_bound_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      fallbackBits + (baseBits + 1) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hsurj

theorem kpoly_anchor_bounded_sample_majority_bit_fallback_family_one_sample_raw_surface_bit_deficit_not_surjective_regression
    {Z : Type v} [Fintype Z] {k fallbackBits baseBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbase :
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ baseBits)
    (hbits :
      fallbackBits + (baseBits + 1) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
      (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
      fallback hbase hbits

end Mettapedia.Computability.PNP.CruxSynthesisRegression
