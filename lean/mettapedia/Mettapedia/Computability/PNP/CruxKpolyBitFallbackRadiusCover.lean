import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds

/-!
# PNP `Kpoly` bit-fallback radius-cover anchors

This module contains the Hamming-radius cover characterization and exact
small-subset/binomial support bounds for bit-coded structured fallback families,
including the zero-fallback-bit sample-bound boundary.
-/

namespace Mettapedia.Computability.PNP
open scoped BigOperators
universe u v w z

/-- Route-coverage anchor: bit-coded structured fallback plus bounded samples
realizes exactly the finite Hamming-radius cover around the lifted fallback
codes. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_realizes_rule_iff_mem_fallbackFamilyRadiusCover
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
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down) rule)

/-- Route-coverage anchor: bit-coded structured fallback plus bounded samples
has predictor image covered by at most one Hamming ball per bit code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_finitePredictorCover
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.FinitePredictorCover
      (2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface,
    card_bitCode] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down))

/-- Route-coverage anchor: bit-coded structured fallback plus bounded samples
is surjective exactly when the lifted fallback-code Hamming cover is the full
rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)
          sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down))

/-- Route-coverage anchor: the exact pointwise repair condition for bit-coded
structured fallback plus bounded samples is radius-`sampleBound` coverage of
every exact-visible rule by some fallback code. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : BitCode fallbackBits,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down))

/-- Route-coverage anchor: full-rule expressivity of a `fallbackBits`-bit
structured fallback family plus bounded samples forces the explicit bit-code
budget times sparse override supports to reach the full exact-visible Boolean
truth-table count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: bit-coded fallback families are full-rule
expressive at full sample radius, independently of the fallback-bit budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_of_surfaceCard_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hbound

/-- Route-coverage anchor: if the explicit bit-code budget times sparse
override supports is below the full truth-table space, then a `fallbackBits`-bit
structured fallback-family endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: the same bit-code obstruction with the sparse
override count expanded as the exact binomial-prefix Hamming-ball support
count. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the bit-code budget times the exact
binomial-prefix Hamming-ball support count is still below the full
exact-visible Boolean rule cube, the endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the exact binomial-prefix Hamming-ball support
count fits into `overheadBits` bits, full expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: if the exact binomial-prefix support envelope fits
into `overheadBits` bits but the total bit budget is still below the
exact-visible alphabet size, then the endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: with no fallback bits, a bounded-sample sparse
override endpoint is not full-rule expressive below the exact-visible alphabet
size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

/-- Route-coverage anchor: with no fallback bits, full-rule expressivity is
equivalent to the sample bound reaching the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback
end Mettapedia.Computability.PNP
