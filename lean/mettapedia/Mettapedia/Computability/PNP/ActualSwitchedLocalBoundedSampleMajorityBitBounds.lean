import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily

/-!
# PNP bounded sample-majority bit-fallback bounds

Bit-coded fallback lower bounds, sample-envelope inequalities, zero-sample thresholds, and bit-budget obstruction lemmas.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- Bit-budget repair burden: if the structured fallback-family endpoint with
`fallbackBits`-bit fallback codes is full-rule expressive, then those codes
times the sparse override supports must cover the full exact-visible Boolean
truth-table cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  classical
  have hlower :
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        Fintype.card (ULift.{v} (BitCode fallbackBits)) *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down) hsurj
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface,
    card_bitCode] using hlower

/-- Bit-coded fallback families are already full-rule expressive once the
sample bound reaches the exact-visible alphabet size.  Extra fallback bits are
irrelevant at this full-radius endpoint. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  exact
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down) hbound

/-- If the bit-code budget times sparse override supports is still below the
exact-visible Boolean truth-table cube, then the `fallbackBits`-bit structured
fallback endpoint cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
      (FallbackIndex := ULift.{v} (BitCode fallbackBits))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fun code => fallback code.down)
  simpa [card_bitCode] using hcard

/-- Binomial-prefix form of the bit-budget repair burden: full-rule
expressivity forces the fallback code count times the exact radius-`sampleBound`
Hamming-ball support count to cover the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ∑ i ∈ Finset.range (sampleBound + 1),
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i := by
  classical
  simpa [PluginSampleMajority.card_smallSubsets_eq_sum_range_choose] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj

/-- If the fallback bits times the binomial-prefix Hamming-ball support count
is still below the Boolean rule cube, then the bit-coded structured fallback
endpoint cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  simpa [PluginSampleMajority.card_smallSubsets_eq_sum_range_choose] using hcard

/-- Exact binomial-prefix bit-budget form: if the radius-`sampleBound`
Hamming-ball support count fits into `overheadBits` bits, then full-rule
expressivity forces the total fallback-plus-overhead bit budget to reach the
exact-visible input alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_sumChooseEnvelope_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  have hbinom :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hbinom.trans hprod)

/-- Strict bit-deficit form for the exact binomial-prefix Hamming-ball support
envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sumChooseEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (∑ i ∈ Finset.range (sampleBound + 1),
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- With zero fallback bits, bounded sampled overrides below the exact-visible
alphabet size cannot be full-rule expressive: one Hamming ball of proper radius
is a strict subset of the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := 0) fallback
  simpa using
    PluginSampleMajority.sum_range_choose_lt_twoPow_of_lt
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hbound

/-- Exact zero-fallback boundary: with no fallback bits, the bit-coded
bounded-sample fallback endpoint is full-rule expressive exactly when the sample
bound reaches the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  classical
  constructor
  · intro hsurj
    by_contra hnot
    have hlt :
        sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
      Nat.lt_of_not_ge hnot
    exact
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        fallback hlt) hsurj
  · intro hbound
    exact
      boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound)
        (fallbackBits := 0) fallback hbound

/-- Coarse polynomial form of the bit-budget repair burden: full-rule
expressivity forces the fallback code count times a polynomial upper envelope on
the sparse override support count to cover the Boolean rule cube. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        ((sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) := by
  classical
  have hbinom :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sum_choose_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hsum :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound :=
    PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow
      (Fintype.card (ExactVisiblePostSwitchSurface Z k)) sampleBound
  exact hbinom.trans (Nat.mul_le_mul_left (2 ^ fallbackBits) hsum)

/-- If even the coarse polynomial fallback-bit envelope is still below the full
Boolean rule cube, then the bit-coded structured fallback endpoint cannot be
full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
    {Z : Type v} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sum_choose_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hsum :
      (∑ i ∈ Finset.range (sampleBound + 1),
        (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose i) ≤
        (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound :=
    PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow
      (Fintype.card (ExactVisiblePostSwitchSurface Z k)) sampleBound
  exact (Nat.mul_le_mul_left (2 ^ fallbackBits) hsum).trans_lt hcard

/-- If the coarse polynomial sparse-override envelope fits into
`overheadBits` bits, then full-rule expressivity forces the total fallback-plus-
override bit budget to reach the exact-visible input alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  have hpoly :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_of_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hpoly.trans hprod)

/-- If the coarse polynomial sparse-override envelope fits into
`overheadBits` bits, but fallback bits plus those overhead bits are still below
the exact-visible alphabet size, then the bit-coded structured fallback endpoint
cannot be full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_sampleBound_succ_mul_surfaceCard_succ_pow_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          ((sampleBound + 1) *
            (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- If the radius multiplier and exact-visible alphabet base have explicit
bit bounds, then full-rule expressivity forces the fallback bits plus those
certified envelope bits to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
  classical
  have henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ (radiusBits + baseBits * sampleBound) :=
    PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hradius hbase
  have htotal :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_polynomialEnvelope_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits)
      (overheadBits := radiusBits + baseBits * sampleBound)
      fallback henvelope hsurj
  simpa [Nat.add_assoc] using htotal

/-- Strict total-bit deficit form using explicit bit bounds for both factors of
the sparse-override polynomial envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
  classical
  have henvelope :
      (sampleBound + 1) *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ^ sampleBound ≤
        2 ^ (radiusBits + baseBits * sampleBound) :=
    PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul
      (n := Fintype.card (ExactVisiblePostSwitchSurface Z k))
      (radius := sampleBound) hradius hbase
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_polynomialEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits)
      (overheadBits := radiusBits + baseBits * sampleBound)
      fallback henvelope
  simpa [Nat.add_assoc] using hbits

/-- If the sample bound itself fits in `radiusBits` bits, full-rule
expressivity still has to pay one more bit for the successor factor
`sampleBound + 1` in the sparse-override envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_base_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits)
      fallback
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
      hbase hsurj

/-- Strict deficit form for the common encoding claim `sampleBound ≤
2 ^ radiusBits`: the extra successor bit is explicit, so it cannot be hidden in
the sparse-override repair budget. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_base_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
    hbase hbits

/-- If the route bounds the sample size and the exact-visible alphabet size
themselves by powers of two, full-rule expressivity still has to pay one extra
bit for each successor appearing in the sparse-override envelope:
`sampleBound + 1` and `surfaceCard + 1`. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_ge_surfaceCard_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_surjective
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_ge_surfaceCard_of_envelopeFactors_le_twoPow_surjective
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits + 1)
      fallback
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
      (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
      hsurj

/-- Strict deficit form when both route-level bit bounds are stated for the
raw sample bound and raw surface-cardinality, rather than their successors. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_sampleBound_le_twoPow_and_surfaceCard_le_twoPow_and_fallbackBits_add_radiusBits_succ_add_baseBits_succ_mul_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_envelopeFactors_le_twoPow_and_fallbackBits_add_radiusBits_add_baseBits_mul_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) (radiusBits := radiusBits + 1) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius)
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hbits

/-- With no sampled overrides, a bit-coded structured fallback family can be
full-rule expressive only if its bit budget reaches the exact-visible input
alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits := by
  classical
  have hpow :
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        2 ^ fallbackBits :=
    by
      simpa using
        boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
          (Z := Z) (k := k) (sampleBound := 0)
          (fallbackBits := fallbackBits) fallback hsurj
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hpow

/-- Equivalently, if the zero-sample structured fallback bit budget is below
the exact-visible input alphabet size, the endpoint cannot be full-rule
expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 0)
      (fallbackBits := fallbackBits) fallback
  simpa using (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits

/-- With zero sampled overrides, the bit-coded fallback endpoint is surjective
exactly when the bit-coded fallback decoder itself is surjective. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    {Z : Type v} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  classical
  constructor
  · intro hsurj rule
    have hfallback :
        Function.Surjective
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down) :=
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
        (FallbackIndex := ULift.{v} (BitCode fallbackBits))
        (Z := Z) (k := k)
        (fallback := fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)).1
        (by
          simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface]
            using hsurj)
    rcases hfallback rule with ⟨code, hcode⟩
    exact ⟨code.down, hcode⟩
  · intro hfallback
    have hwrapped :
        Function.Surjective
          (fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down) := by
      intro rule
      rcases hfallback rule with ⟨code, hcode⟩
      exact ⟨ULift.up code, hcode⟩
    simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
        (FallbackIndex := ULift.{v} (BitCode fallbackBits))
        (Z := Z) (k := k)
        (fallback := fun code : ULift.{v} (BitCode fallbackBits) => fallback code.down)).2
        hwrapped

end Mettapedia.Computability.PNP
