import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Fallback-family radius-cover regressions

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (fallback : U → Bool) (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.disagreementSupport fallback
      (fun u : U =>
        PluginSampleMajority.predictWithFallback fallback sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.disagreementSupport_predictWithFallback_card_le_bound
    fallback sample

example {FallbackIndex Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback index

example {FallbackIndex Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule hcard

example {U : Type} [Fintype U] (reference : U → Bool) (s : Finset U) :
    PluginSampleMajority.disagreementSupport reference
      (PluginSampleMajority.flipOn reference s) = s :=
  PluginSampleMajority.disagreementSupport_flipOn reference s

example {U : Type} [Fintype U] (reference : U → Bool) (radius : ℕ) :
    (PluginSampleMajority.disagreementBall reference radius).card ≤
      (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.disagreementBall_card_le_smallSubsets_card
    reference radius

example {FallbackIndex U : Type} [Fintype FallbackIndex] [Fintype U]
    (fallback : FallbackIndex → U → Bool) (radius : ℕ) :
    (PluginSampleMajority.fallbackFamilyRadiusCover fallback radius).card ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.fallbackFamilyRadiusCover_card_le fallback radius

example {FallbackIndex U : Type} [Fintype FallbackIndex] [Fintype U] [DecidableEq U]
    (fallback : FallbackIndex → U → Bool) {radius : ℕ}
    (hcover :
      PluginSampleMajority.fallbackFamilyRadiusCover fallback radius =
        (Finset.univ : Finset (U → Bool))) :
    2 ^ Fintype.card U ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets U radius).card :=
  PluginSampleMajority.boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
    fallback hcover

example {U : Type} [DecidableEq U]
    (fallback rule : U → Bool) (support : Finset U)
    (hoff : ∀ u : U, u ∉ support → fallback u = rule u) :
    PluginSampleMajority.predictWithFallback fallback
        (PluginSampleMajority.supportSample support rule) =
      rule :=
  PluginSampleMajority.predictWithFallback_supportSample_eq_of_eq_off_support
    fallback rule support hoff

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hcard

example {FallbackIndex Z : Type} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback hsurj

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
