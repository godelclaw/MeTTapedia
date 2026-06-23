import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajoritySparseThresholdERMObstruction


/-!
# PNP `Kpoly` actual-local plug-in family anchors

Plug-in lookup, plug-in majority, and sample-majority surjectivity and exact-visible budget obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a bare plug-in lookup table over the exact visible
alphabet is already surjective onto all exact-visible Boolean rules. -/
theorem kpolyCoverage_anchor_pluginLookup_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginLookupActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: the bare plug-in lookup endpoint has no clocked
finite-learning payload below the full exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginLookup_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginLookupActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: a bare plug-in lookup endpoint cannot be identified
with bounded ZAB decision-list constructor data below the exact-visible
truth-table budget. -/
theorem kpolyCoverage_anchor_pluginLookup_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) :=
  pluginLookupActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: unrestricted plug-in majority counts are already
surjective onto all exact-visible Boolean rules. -/
theorem kpolyCoverage_anchor_pluginMajority_surjective
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginMajorityActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: unrestricted plug-in majority counts have no clocked
finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: unrestricted plug-in majority cannot be treated as
bounded ZAB decision-list constructor data below the exact-visible truth-table
budget. -/
theorem kpolyCoverage_anchor_pluginMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: sample-level plug-in majority is still surjective
onto all exact-visible Boolean rules via graph samples. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_surjective
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict :=
  pluginSampleMajorityActualSwitchedLocalInterface_surjective Z k

/-- Route-coverage anchor: sample-level plug-in majority has no clocked
finite-learning payload below the exact-visible truth-table budget. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hs

/-- Route-coverage anchor: sample-level plug-in majority cannot be treated as
bounded ZAB decision-list constructor data below the exact-visible truth-table
budget. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    zfeat hs

/-- Route-coverage anchor: unrestricted sample-level plug-in majority cannot
be identified with one shared exact sparse-threshold ERM family below the
point-block visible-budget threshold. -/
theorem kpolyCoverage_anchor_pluginSampleMajority_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k)
          zfeat) :=
  pluginSampleMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (Z := Z) (k := k) zfeat hs

end Mettapedia.Computability.PNP
