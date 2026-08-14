import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# Kernel-reduced incoming-profile data on the first-IBP row

This module isolates the finite first-IBP replay needed to test the existing
scalar deformation.  It is an exact kernel computation, not a descent claim.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingIBPData

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ourIBP_incomingPlaneProfileSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 1 3) ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ)) =
      0 := by
  fin_cases field <;> decide +kernel

#print axioms ourIBP_incomingPlaneProfileSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderIncomingIBPData
