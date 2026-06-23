import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Fallback-family surjectivity regressions

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example {U : Type} [Fintype U] (reference rule : U → Bool) :
    (PluginSampleMajority.disagreementSupport reference rule).card ≤
      Fintype.card U :=
  PluginSampleMajority.disagreementSupport_card_le_card reference rule

example {FallbackIndex U : Type} [Fintype FallbackIndex]
    [Nonempty FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcard : Fintype.card U ≤ radius) (rule : U → Bool) :
    rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback radius :=
  PluginSampleMajority.mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
    (fallback := fallback) hcard rule

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    (FallbackIndex := FallbackIndex) (Z := Z) (k := k)
    (sampleBound := sampleBound) fallback hbound

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

example {FallbackIndex Z : Type} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) fallback

example {Z : Type} {k sampleBound fallbackBits : ℕ} [Fintype Z]
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound fallbackBits fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_of_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound)
    (fallbackBits := fallbackBits) fallback hbound

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : BitCode 0 → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k sampleBound 0 fallback).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroFallbackBits_surjective_iff_surfaceCard_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {Z : Type} {k sampleBound : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k sampleBound (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_exactVisibleRuleDecode
    (Z := Z) (k := k) (sampleBound := sampleBound)

example {Z : Type} {k fallbackBits : ℕ}
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
          Z k 0 fallbackBits fallback).predictorFamily.predict ↔
      Function.Surjective fallback :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    (Z := Z) (k := k) (fallbackBits := fallbackBits) fallback

example {Z : Type} {k : ℕ} [Fintype Z] :
    Function.Surjective
      (boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
        Z k 0 (Fintype.card (ExactVisiblePostSwitchSurface Z k))
        (exactVisibleRuleDecode (Z := Z) (k := k))).predictorFamily.predict :=
  boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface_surjective_zeroSample_exactVisibleRuleDecode
    (Z := Z) (k := k)

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
