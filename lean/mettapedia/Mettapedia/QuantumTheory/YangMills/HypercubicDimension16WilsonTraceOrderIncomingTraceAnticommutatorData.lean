import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

/-!
# Kernel-reduced incoming-profile data on the trace-anticommutator row

This module isolates the three finite signed-orbit calculations needed to
test OUR existing scalar deformation on the actual polarized trace row.  It is
an exact replay of this named relation, not a descent claim.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingTraceAnticommutatorData

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourTraceAnticommutatorBase_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourTraceAnticommutatorSwap_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourTraceAnticommutatorSplit_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourTraceAnticommutatorBase_incomingPlaneProfileSignedWeight
#print axioms ourTraceAnticommutatorSwap_incomingPlaneProfileSignedWeight
#print axioms ourTraceAnticommutatorSplit_incomingPlaneProfileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingTraceAnticommutatorData
