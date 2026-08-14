import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-! # Kernel-reduced incoming profile: first two EOM terms -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock00

open V14HypercubicFDCensus V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourEOMZero_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourEOMOne_incomingPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourEOMZero_incomingPlaneProfileSignedWeight
#print axioms ourEOMOne_incomingPlaneProfileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingEOMDataBlock00
