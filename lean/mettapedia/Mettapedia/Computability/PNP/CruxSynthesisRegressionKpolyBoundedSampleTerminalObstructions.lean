import Mettapedia.Computability.PNP.CruxKpolySampleMajorityTerminalObstructions

/-!
# Regression checks for PNP Kpoly bounded-sample anchors: terminal non-payload and ZAB-data obstruction checks

This module is part of the decomposed bounded-sample Kpoly regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_bounded_sample_majority_no_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (sampleBound := sampleBound)
      (clock := clock) hbound hs

theorem kpoly_anchor_bounded_sample_majority_no_zab_data_regression
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) := by
  exact
    kpolyCoverage_anchor_boundedSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
      (Z := Z) (k := k) (r := r) (sampleBound := sampleBound)
      hbound zfeat hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
