import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# PNP `Kpoly` bit-fallback sample-envelope anchors

This file contains one- and two-sample support-envelope and bit-deficit anchors
for bit-coded fallback endpoints in the `Kpoly` bridge. Sparse-threshold
recovery barriers live in `CruxKpolyBitFallbackThresholdAnchors`.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: with one sampled sparse override, full-rule
expressivity of a bit-coded structured fallback endpoint forces the concrete
budget `2 ^ fallbackBits * (surfaceCard + 1)`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the one-sample bit-coded fallback budget times
`surfaceCard + 1` is still below the full exact-visible Boolean rule cube, the
endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: allowing two sampled sparse overrides gives exactly
the quadratic support multiplier `1 + surfaceCard + choose surfaceCard 2`; full
rule expressivity must fit inside this product budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: a bit-coded structured fallback plus two sampled
overrides is not full-rule expressive when its exact quadratic product budget
is below the Boolean rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the exact two-sample quadratic support envelope
fits into `overheadBits` bits, full rule coverage still forces the total
fallback-plus-overhead bit budget to reach the visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: strict bit deficit against the exact two-sample
quadratic support envelope blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
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
        Z k 2 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: with one sampled sparse override, a successor bit
bound for `surfaceCard + 1` converts the exact product bound into the additive
bit budget `fallbackBits + baseBits`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
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
      fallbackBits + baseBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Route-coverage anchor: strict bit deficit for the exact one-sample
successor-count envelope blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
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
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

/-- Route-coverage anchor: if the manuscript route states only a raw bit bound
on `surfaceCard`, the one-sample sparse-support envelope still needs one extra
successor bit. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
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
      fallbackBits + (baseBits + 1) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hsurj

/-- Route-coverage anchor: strict bit deficit for the raw one-sample
surface-cardinality bound blocks full-rule expressivity. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
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
        Z k 1 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits)
    fallback hbase hbits

end Mettapedia.Computability.PNP
