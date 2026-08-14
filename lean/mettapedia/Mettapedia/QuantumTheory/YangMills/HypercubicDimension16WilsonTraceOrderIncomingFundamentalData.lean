import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

/-!
# Kernel-reduced incoming-profile data on the fundamental three-cut row

This module isolates the six finite signed-orbit calculations needed to test
OUR existing scalar deformation on the actual fundamental trace row.  It is an
exact replay of this named relation, not a descent claim.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingFundamentalData

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutBase_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutSwapFirstSecond_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutSwapFirstThird_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutSwapSecondThird_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutForward_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourFundamentalThreeCutBackward_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourFundamentalThreeCutBase_incomingPlaneProfileSignedWeight
#print axioms ourFundamentalThreeCutSwapFirstSecond_incomingPlaneProfileSignedWeight
#print axioms ourFundamentalThreeCutSwapFirstThird_incomingPlaneProfileSignedWeight
#print axioms ourFundamentalThreeCutSwapSecondThird_incomingPlaneProfileSignedWeight
#print axioms ourFundamentalThreeCutForward_incomingPlaneProfileSignedWeight
#print axioms ourFundamentalThreeCutBackward_incomingPlaneProfileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingFundamentalData
