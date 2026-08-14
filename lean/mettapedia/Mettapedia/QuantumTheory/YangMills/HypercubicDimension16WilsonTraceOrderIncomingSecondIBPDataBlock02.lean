import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-! # Kernel-reduced incoming profile: second-IBP summands 4 and 5 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock02

open V14HypercubicFDCensus V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_incomingPlaneProfileSignedWeight_four :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm (4 : Fin 7)).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm (4 : Fin 7)).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourSecondIBP_incomingPlaneProfileSignedWeight_five :
    (∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm (5 : Fin 7)).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3)
          ((ourSecondIBPLabeledTerm (5 : Fin 7)).hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

#print axioms ourSecondIBP_incomingPlaneProfileSignedWeight_four
#print axioms ourSecondIBP_incomingPlaneProfileSignedWeight_five

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingSecondIBPDataBlock02
