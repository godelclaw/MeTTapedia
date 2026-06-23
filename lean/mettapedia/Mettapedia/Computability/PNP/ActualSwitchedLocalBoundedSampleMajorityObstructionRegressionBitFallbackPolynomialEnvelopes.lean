import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Bit-fallback polynomial-envelope regressions

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hsurj

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hsurj

example {Z : Type} {k sampleBound fallbackBits radiusBits baseBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (radiusBits := radiusBits) (baseBits := baseBits)
    fallback hradius hbase hbits

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ fallbackBits :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_fallbackBits_ge_surfaceCard_of_zeroSample_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hsurj

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbits : fallbackBits < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroSample_of_fallbackBits_lt_surfaceCard
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback hbits

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits overheadBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
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

example {Z : Type} {k fallbackBits baseBits : ℕ} [Fintype Z]
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

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
