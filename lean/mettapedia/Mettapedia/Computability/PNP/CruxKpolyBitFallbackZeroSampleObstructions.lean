import Mettapedia.Computability.PNP.ActualSwitchedLocalBitFallbackZeroSampleImage
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackPolynomialEnvelope
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# PNP `Kpoly` bit-fallback zero-sample obstruction anchors

This module contains the zero-sample fallback-bit lower bound and canonical
exact-visible decoder finite-cover/realization obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: without sampled sparse overrides, a bit-coded
structured fallback family can be full-rule expressive only if the fallback bit
budget reaches the exact-visible input alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

/-- Route-coverage anchor: a zero-sample bit-coded structured fallback endpoint
is not full-rule expressive when its fallback bit budget is below the
exact-visible input alphabet size. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

/-- Route-coverage anchor: the zero-sample lower bound is sharp for the
canonical full truth-table fallback decoder.  At exactly one fallback bit per
exact-visible input, the empty sample already realizes every local rule. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
    {Z : Type v} [Fintype Z] {k : ℕ} :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    (Z := Z) (k := k)

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already has no finite predictor-image cover below
the full Boolean rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorCover (2 ^ s) := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exactVisible_finitePredictorCover_of_surjective_predict
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)
      (N := 2 ^ s) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
        (Z := Z) (k := k))

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already has no finite selected-index
representative cover below the full Boolean rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finiteIndexRepresentativeCover_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FiniteIndexRepresentativeCover (2 ^ s) := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)
      (N := 2 ^ s) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
        (Z := Z) (k := k))

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already has no finite quotient-code presentation
below the full Boolean rule cube. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorQuotient_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorQuotient (2 ^ s) := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exactVisible_finitePredictorQuotient_of_surjective_predict
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)
      (N := 2 ^ s) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
        (Z := Z) (k := k))

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already admits no exact-visible compression target
below the truth-table bit budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exactVisibleCompressionTarget_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BitFallbackZeroSampleImage.ZeroSampleIndex
          Z k (Fintype.card (ExactVisiblePostSwitchSurface Z k)))
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily s := by
  intro hcomp
  have hcover :
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)).1 hcomp
  exact
    kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs hcover

/-- Route-coverage anchor: at zero sample radius, the canonical exact-visible
truth-table fallback decoder already admits no clocked exact-visible
realization below the truth-table bit budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_zeroSample_exactVisibleRuleDecode_not_exists_clockedExactVisibleRealization_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
          (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.RealizedByClockedBitFamily F := by
  have hpow : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact
    not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
      (G := (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily)
      (clock := clock) hpow
      (kpolyCoverage_anchor_boundedSampleMajorityWithBitFallbackFamily_surjective_zeroSample_exactVisibleRuleDecode
        (Z := Z) (k := k))
end Mettapedia.Computability.PNP
