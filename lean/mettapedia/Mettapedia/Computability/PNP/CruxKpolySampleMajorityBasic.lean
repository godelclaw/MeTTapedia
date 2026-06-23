import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces


/-!
# PNP `Kpoly` sample-majority anchors: basic bounded majority

Basic bounded sample-majority thresholds and explicit-default tie-break anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: bounded sample-level plug-in majority is full-rule
expressive exactly when the sample bound reaches the exact-visible alphabet
size. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_surjective_iff
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff
    Z k sampleBound

/-- Route-coverage anchor: every predictor selected by bounded sample-level
plug-in majority is false on at most `sampleBound` exact-visible inputs. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_falseSupport_card_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) sample

/-- Route-coverage anchor: a target rule whose false-support exceeds the
sample bound is not realized by bounded sample-level plug-in majority. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) rule hcard

/-- Route-coverage anchor: with any explicit tie-breaking default, every
bounded sample-level plug-in majority predictor differs from that default on at
most `sampleBound` exact-visible inputs. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_nondefaultSupport_card_le_sampleBound
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    (Z := Z) (k := k) (sampleBound := sampleBound) default sample

/-- Route-coverage anchor: for any tie-breaking default, a target rule whose
nondefault support exceeds the sample bound is not realized by bounded
sample-level plug-in majority. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    {Z : Type v} [Fintype Z] {k sampleBound : ℕ}
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    (Z := Z) (k := k) (sampleBound := sampleBound) default rule hcard

/-- Route-coverage anchor: changing the bounded plug-in majority tie-break does
not change the exact surjectivity threshold. -/
theorem kpolyCoverage_anchor_boundedSampleMajorityWithDefault_surjective_iff
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound :=
  boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    default Z k sampleBound


end Mettapedia.Computability.PNP
