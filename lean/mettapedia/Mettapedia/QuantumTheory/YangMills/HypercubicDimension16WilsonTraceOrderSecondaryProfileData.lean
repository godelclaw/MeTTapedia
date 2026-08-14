import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# Kernel-reduced secondary commutator cycle-profile data

This narrow certificate module keeps the two finite signed sums independent of
the semantic assembly that consumes them.  Both are exact kernel reductions.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryProfileData

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySource_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourSecondarySourceLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySwapped_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourSecondarySwappedLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

#print axioms ourSecondarySource_profileSignedWeight
#print axioms ourSecondarySwapped_profileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryProfileData
