import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-! # Kernel-reduced incoming profile: second-IBP summand 6 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock03

open V14HypercubicFDCensus V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_incomingPlaneProfileSignedWeight_six :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm (6 : Fin 7)).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm (6 : Fin 7)).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourSecondIBP_incomingPlaneProfileSignedWeight_six

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock03
