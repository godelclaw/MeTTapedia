import Mettapedia.Computability.PNP.CruxKpolySampleMajorityFallbackFamilyRadiusCover

/-!
# PNP `Kpoly` sample-majority anchors: terminal payload obstructions

Terminal clocked-payload and ZAB-decision-list barriers for bounded sample-majority endpoints.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, bounded sample-level plug-in majority has no clocked
finite-learning payload below the truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s sampleBound clock : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    hbound hs

/-- Route-coverage anchor: once the sample bound reaches the exact-visible
alphabet size, bounded sample-level plug-in majority still cannot be treated as
bounded ZAB decision-list constructor data below the truth-table budget. -/
theorem kpolyCoverage_anchor_boundedSampleMajority_not_zabDecisionListData_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    hbound zfeat hs


end Mettapedia.Computability.PNP
