import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Plug-in majority and singleton-fallback regressions

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example (Z : Type) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective Z k sampleBound hbound

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) hbound

example (Z : Type) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff Z k sampleBound

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : U => PluginSampleMajority.predict sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.falseSupport_predict_card_le_bound sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

example {U : Type} [Fintype U] [DecidableEq U] {sampleBound : ℕ}
    (default : Bool) (sample : BoundedSampleIndex U sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : U =>
        PluginSampleMajority.predictWithDefault default sample.1 u)).card ≤ sampleBound :=
  PluginSampleMajority.nondefaultSupport_predictWithDefault_card_le_bound default sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) default sample

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

example {Z : Type} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    (Z := Z) (k := k) (sampleBound := sampleBound) default hbound

example (Z : Type) (k sampleBound : ℕ) [Fintype Z] (default : Bool) :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    default Z k sampleBound

example {U : Type} [DecidableEq U] (fallback : U → Bool) (u : U) :
    PluginSampleMajority.predictWithFallback fallback ([] : Sample U Bool) u =
      fallback u :=
  PluginSampleMajority.predictWithFallback_nil fallback u

example {Z : Type} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    (Z := Z) (k := k) (sampleBound := sampleBound) fallback

example (Z : Type) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    Z k sampleBound

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hs

example {Z : Type} {k s sampleBound clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock :=
  boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hs

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
