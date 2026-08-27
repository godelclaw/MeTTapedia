import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-! # Kernel-reduced incoming profile: second-IBP summands 2 and 3 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock01

open V14HypercubicFDCensus V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_incomingPlaneProfileSignedWeight_two :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm (2 : Fin 7)).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm (2 : Fin 7)).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_incomingPlaneProfileSignedWeight_three :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm (3 : Fin 7)).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm (3 : Fin 7)).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourSecondIBP_incomingPlaneProfileSignedWeight_two
#print axioms ourSecondIBP_incomingPlaneProfileSignedWeight_three

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock01
