import Mettapedia.Computability.PNP.CruxKpolyBitFallbackRadiusCover

/-!
# PNP `Kpoly` bit-fallback polynomial-envelope anchors

This module packages coarse polynomial support envelopes and additive bit-budget
consequences for bit-coded bounded-sample fallback endpoints.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a coarse polynomial envelope of the exact
binomial-prefix sparse override count is already enough to state the fallback
bit-budget burden in a directly asymptotic-looking form. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: if the bit-code budget times the coarse polynomial
Hamming-ball envelope is below the full exact-visible Boolean rule cube, then
the bit-coded structured fallback endpoint is not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    {Z : Type v} [Fintype Z] {k sampleBound fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hcard

/-- Route-coverage anchor: if the sampled sparse-override polynomial envelope
fits into `overheadBits` bits, then full expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
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
      fallbackBits + overheadBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hsurj

/-- Route-coverage anchor: if the sparse-override polynomial envelope fits into
`overheadBits` bits but `fallbackBits + overheadBits` is still below the
exact-visible alphabet size, then the bit-coded structured fallback endpoint is
not full-rule expressive. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (overheadBits := overheadBits)
    fallback henvelope hbits

/-- Route-coverage anchor: explicit bit bounds for the radius multiplier and
visible-alphabet base turn the polynomial envelope into the additive budget
`radiusBits + baseBits * sampleBound`. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
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
      fallbackBits + radiusBits + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict total-bit deficit after separately bounding
the radius and base factors blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

/-- Route-coverage anchor: when the route only proves `sampleBound ≤
2 ^ radiusBits`, the successor factor in the sparse-support envelope costs one
extra radius bit. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
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
      fallbackBits + (radiusBits + 1) + baseBits * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict bit deficit after paying the successor bit for
the radius multiplier blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

/-- Route-coverage anchor: if both the sample bound and the surface-cardinality
bound are stated for the raw values, the sparse-support envelope charges one
successor bit for each of them. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
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
      fallbackBits + (radiusBits + 1) + (baseBits + 1) * sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

/-- Route-coverage anchor: strict bit deficit after paying both successor bits
blocks the bit-coded structured fallback endpoint. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
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
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits
end Mettapedia.Computability.PNP
