import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# Kernel-reduced secondary commutator derivative-axis data

This narrow certificate module keeps the two finite signed sums independent of
the semantic assembly that consumes them.  Both are exact kernel reductions.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryAxisData

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open SU2LatticeFDCensusNoGo
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySource_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourSecondarySourceLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourSecondarySourceLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondarySwapped_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourSecondarySwappedLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourSecondarySwappedLabeled.hypercubicAct h) : ℚ)) = -32 := by
  decide +kernel

#print axioms ourSecondarySource_signedAxisWeight
#print axioms ourSecondarySwapped_signedAxisWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderSecondaryAxisData
