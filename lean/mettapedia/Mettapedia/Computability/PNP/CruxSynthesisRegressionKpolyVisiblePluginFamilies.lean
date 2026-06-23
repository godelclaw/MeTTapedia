import Mettapedia.Computability.PNP.CruxKpolyActualLocalPluginFamilies

/-!
# CruxSynthesisRegressionKpolyVisiblePluginFamilies

Plugin lookup, plugin majority, and plugin sample-majority regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_plugin_lookup_surjective_regression
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginLookup_surjective Z k

theorem kpoly_anchor_plugin_lookup_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginLookupActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginLookup_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_lookup_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginLookupActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginLookup_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

theorem kpoly_anchor_plugin_majority_surjective_regression
    (Z : Type v) (k : ℕ) :
    Function.Surjective
      (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginMajority_surjective Z k

theorem kpoly_anchor_plugin_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

theorem kpoly_anchor_plugin_sample_majority_surjective_regression
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Function.Surjective
      (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily.predict := by
  exact kpolyCoverage_anchor_pluginSampleMajority_surjective Z k

theorem kpoly_anchor_plugin_sample_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (pluginSampleMajorityActualSwitchedLocalInterface Z k).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_pluginSampleMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem kpoly_anchor_plugin_sample_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r : ℕ}
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (pluginSampleMajorityActualSwitchedLocalInterface Z k) zfeat) := by
  exact
    kpolyCoverage_anchor_pluginSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) zfeat hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
