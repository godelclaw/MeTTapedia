import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# Kernel-reduced secondary commutator first-IBP data

This narrow certificate module keeps the two finite signed sums independent of
the semantic assembly that consumes them.  Both are exact kernel reductions.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryIBPData

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySource_IBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourSecondarySourceLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySwapped_IBPAxisPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourSecondarySource_IBPAxisPlanePairSignedWeight
#print axioms ourSecondarySwapped_IBPAxisPlanePairSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryIBPData
