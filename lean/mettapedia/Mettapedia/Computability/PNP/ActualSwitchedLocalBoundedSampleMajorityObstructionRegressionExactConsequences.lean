import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences

/-!
# Exact-cover obstruction consequences

Regression examples split out of the bounded-sample plug-in majority obstruction hub.
The examples are copied unchanged from the historical broad regression module.
-/

namespace Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression

open Mettapedia.Computability.PNP

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hbound hs

example {Z : Type} {k s sampleBound clock : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily
        s clock :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) (clock := clock) hbound hs

example {Z : Type} {k s sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.BitCodeData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) s) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_bitCodeData_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (sampleBound := sampleBound) hbound hs

example {Z : Type} {k r sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (zfeat : Z → BitVec r)
    (hs : r + 2 * k + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (ActualSwitchedLocalInterface.ZABDecisionListData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound) zfeat) :=
  boundedSamplePluginMajorityActualSwitchedLocalInterface_not_zabDecisionListData_of_lt_surfaceCard
    (Z := Z) (k := k) (r := r) (sampleBound := sampleBound) hbound zfeat hs

end Mettapedia.Computability.PNP.BoundedSampleMajorityObstructionRegression
