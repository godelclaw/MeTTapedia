import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-! # Kernel-reduced incoming profile: second Bianchi rotation -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock01

open V14HypercubicFDCensus V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourBianchiRotateTwo_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

#print axioms ourBianchiRotateTwo_incomingPlaneProfileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingBianchiDataBlock01
