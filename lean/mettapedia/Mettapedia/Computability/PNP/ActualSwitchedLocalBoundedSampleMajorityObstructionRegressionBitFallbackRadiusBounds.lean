import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Bit-fallback radius and choose-sum bounds

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {U : Type} [Fintype U] {radius : ℕ} :
    (PluginSampleMajority.smallSubsets U radius).card =
      ∑ i ∈ Finset.range (radius + 1), (Fintype.card U).choose i :=
  PluginSampleMajority.card_smallSubsets_eq_sum_range_choose (U := U) radius

example {n radius : ℕ} :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) ≤
      (radius + 1) * (n + 1) ^ radius :=
  PluginSampleMajority.sum_range_choose_le_succ_mul_succ_pow n radius

example {U : Type} [Fintype U] {radius : ℕ} :
    (PluginSampleMajority.smallSubsets U radius).card ≤
      (radius + 1) * (Fintype.card U + 1) ^ radius :=
  PluginSampleMajority.card_smallSubsets_le_succ_mul_succ_card_pow (U := U) radius

example {U : Type} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    PluginSampleMajority.smallSubsets U radius ⊂
      (Finset.univ : Finset (Finset U)) :=
  PluginSampleMajority.smallSubsets_ssubset_univ_of_radius_lt_card
    (U := U) (radius := radius) hradius

example {U : Type} [Fintype U] {radius : ℕ}
    (hradius : radius < Fintype.card U) :
    (PluginSampleMajority.smallSubsets U radius).card <
      2 ^ Fintype.card U :=
  PluginSampleMajority.card_smallSubsets_lt_twoPow_card_of_radius_lt_card
    (U := U) (radius := radius) hradius

example {n radius : ℕ} (hradius : radius < n) :
    (∑ i ∈ Finset.range (radius + 1), n.choose i) < 2 ^ n :=
  PluginSampleMajority.sum_range_choose_lt_twoPow_of_lt
    (n := n) (radius := radius) hradius

example {n radius radiusBits baseBits : ℕ}
    (hradius : radius + 1 ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ (radiusBits + baseBits * radius) :=
  PluginSampleMajority.succ_mul_succ_pow_le_twoPow_add_mul hradius hbase

example {radius radiusBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits) :
    radius + 1 ≤ 2 ^ (radiusBits + 1) :=
  PluginSampleMajority.succ_le_twoPow_succ_of_le_twoPow hradius

example {n radius radiusBits baseBits : ℕ}
    (hradius : radius ≤ 2 ^ radiusBits)
    (hbase : n + 1 ≤ 2 ^ baseBits) :
    (radius + 1) * (n + 1) ^ radius ≤
      2 ^ ((radiusBits + 1) + baseBits * radius) :=
  PluginSampleMajority.succ_mul_succ_pow_le_twoPow_succ_add_mul hradius hbase

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hsurj

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    fallback hcard

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hsurj

example {Z : Type} {k sampleBound fallbackBits overheadBits : ℕ} [Fintype Z]
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
    (Z := Z) (k := k) (sampleBound := sampleBound) (fallbackBits := fallbackBits)
    (overheadBits := overheadBits) fallback henvelope hbits

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k)
    (hbound :
      sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound 0 fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_not_surjective_zeroFallbackBits_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hbound

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
