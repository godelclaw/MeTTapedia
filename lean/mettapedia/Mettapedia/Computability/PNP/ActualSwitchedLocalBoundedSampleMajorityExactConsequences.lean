import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds

/-!
# PNP bounded sample-majority exact decoder consequences

Exact visible rule decoders, one- and two-sample consequences, and downstream finite-cover/bit-code/ZAB-data obstruction wrappers.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- At the full exact-visible truth-table bit budget, the canonical decoder is
full-rule expressive for every sample bound.  The proof uses the empty sample,
so bounded sampled overrides do not contribute to expressivity here. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  classical
  simpa [boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface] using
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
      (FallbackIndex :=
        ULift.{v} (BitCode (Fintype.card (ExactVisiblePostSwitchSurface Z k))))
      (Z := Z) (k := k) (sampleBound := sampleBound)
      (fallback := fun code =>
        exactVisibleRuleDecode (Z := Z) (k := k) code.down)
      (by
        intro rule
        refine ⟨ULift.up (exactVisibleRuleEncode (Z := Z) (k := k) rule), ?_⟩
        simpa using exactVisibleRuleDecode_encode (Z := Z) (k := k) rule))

/-- The zero-sample lower bound is sharp for the canonical full truth-table
fallback decoder: with exactly one bit per exact-visible input, the empty
sample leaves the decoded fallback rule unchanged. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    {Z : Type v} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict := by
  exact
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
      (Z := Z) (k := k) (sampleBound := 0)

/-- With one sampled override, full-rule expressivity of a bit-coded structured
fallback family forces the explicit multiplier `surfaceCard + 1`: either no
override is used, or exactly one exact-visible input is overwritten. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 1 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) := by
  classical
  simpa using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := 1)
      (fallbackBits := fallbackBits) fallback hsurj

/-- Consequently, if the one-sample bit-code budget times `surfaceCard + 1` is
still below the full exact-visible Boolean rule cube, the endpoint cannot be
full-rule expressive. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 1 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 1)
      (fallbackBits := fallbackBits) fallback
  simpa using hcard

/-- With two sampled overrides, full-rule expressivity of a bit-coded
structured fallback family forces the explicit quadratic sparse-support
multiplier `1 + surfaceCard + choose surfaceCard 2`. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 2 fallbackBits fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 ^ fallbackBits *
        (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
          (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) := by
  classical
  simpa [PluginSampleMajority.card_smallSubsets_two, Nat.add_assoc] using
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_smallSubsets_card_of_surjective
      (Z := Z) (k := k) (sampleBound := 2)
      (fallbackBits := fallbackBits) fallback hsurj

/-- Strict product-deficit form for the exact two-sample quadratic sparse
support envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
    {Z : Type v} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hcard :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 2 fallbackBits fallback).predictorFamily.predict := by
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_bitCode_mul_smallSubsets_card_lt_boolClassifierSpace
      (Z := Z) (k := k) (sampleBound := 2)
      (fallbackBits := fallbackBits) fallback
  simpa [PluginSampleMajority.card_smallSubsets_two, Nat.add_assoc] using hcard

/-- If the exact two-sample quadratic sparse-support envelope fits into
`overheadBits` bits, full-rule expressivity forces the total
fallback-plus-overhead bit budget to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_overheadBits_ge_surfaceCard_of_twoSample_quadraticEnvelope_le_twoPow_surjective
    {Z : Type v} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  have hquad :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_one_add_surfaceCard_add_choose_two_of_twoSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hquad.trans hprod)

/-- Strict bit-deficit form for the exact two-sample quadratic sparse-support
envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_quadraticEnvelope_le_twoPow_and_fallbackBits_add_overheadBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_twoSample_of_bitCode_mul_one_add_surfaceCard_add_choose_two_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
        2 ^ (fallbackBits + overheadBits) := by
    calc
      2 ^ fallbackBits *
          (1 + Fintype.card (ExactVisiblePostSwitchSurface Z k) +
            (Fintype.card (ExactVisiblePostSwitchSurface Z k)).choose 2) ≤
          2 ^ fallbackBits * 2 ^ overheadBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) henvelope
      _ = 2 ^ (fallbackBits + overheadBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- One sampled override has the exact sparse-support count `surfaceCard + 1`.
Thus, if that successor count fits in `baseBits` bits, full-rule expressivity
forces `fallbackBits + baseBits` to reach the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
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
  classical
  have hcover :=
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_bitCode_mul_surfaceCard_succ_of_oneSample_surjective
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj
  have hprod :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
        2 ^ (fallbackBits + baseBits) := by
    calc
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
          2 ^ fallbackBits * 2 ^ baseBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) hbase
      _ = 2 ^ (fallbackBits + baseBits) := by
        rw [← pow_add]
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hcover.trans hprod)

/-- Strict bit-deficit form for the exact one-sample successor-count envelope. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
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
  classical
  apply
    boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_bitCode_mul_surfaceCard_succ_lt_boolClassifierSpace
      (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback
  have hprod :
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
        2 ^ (fallbackBits + baseBits) := by
    calc
      2 ^ fallbackBits *
          (Fintype.card (ExactVisiblePostSwitchSurface Z k) + 1) ≤
          2 ^ fallbackBits * 2 ^ baseBits :=
        Nat.mul_le_mul_left (2 ^ fallbackBits) hbase
      _ = 2 ^ (fallbackBits + baseBits) := by
        rw [← pow_add]
  exact hprod.trans_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hbits)

/-- If the route states only a raw bit bound on `surfaceCard`, the one-sample
successor count still costs one additional bit. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_succ_ge_surfaceCard_of_oneSample_surfaceCard_le_twoPow_surjective
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
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
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_add_baseBits_ge_surfaceCard_of_oneSample_surfaceCard_succ_le_twoPow_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hsurj

/-- Strict bit-deficit form for the raw one-sample surface-cardinality bound. -/
theorem boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_le_twoPow_and_fallbackBits_add_baseBits_succ_lt_surfaceCard
    {Z : Type v} {k fallbackBits baseBits : ℕ} [Fintype Z]
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
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_oneSample_of_surfaceCard_succ_le_twoPow_and_fallbackBits_add_baseBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) (baseBits := baseBits + 1)
    fallback
    (PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hbase)
    hbits

/-- A sample-size bound at least the visible alphabet size still gives no small
finite predictor cover below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)) hsmall

/-- Consequently the same bounded-sample endpoint cannot provide the clocked
finite-learning payload below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound clock : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)) hsmall

/-- Such a sample-size bound is also insufficient for the bounded-code minimal
missing assumption below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) s) := by
  rintro ⟨hcode⟩
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound)
      hbound hs hcode.finitePredictorCover

/-- Such a sample-size bound is insufficient for the ZAB decision-list
constructor data below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} {k r sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) := by
  rintro ⟨hzab⟩
  exact
    hzab.not_surjective_predict_of_lt_surfaceCard hs
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hbound)

end Mettapedia.Computability.PNP
