import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM

/-! Regression checks for OUR invariant EOM trace-order test. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantEOM

example :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero

example :
    ourInvariantEOMRow ∈ jointInvariantRelationSubmodule .onShell :=
  ourInvariantEOMRow_mem

example :
    ourTwoCoordinateInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_invariantEOM_zero

#print axioms HypercubicDimension16WilsonTraceOrderInvariantEOM.ourEOMZero_signedAxisWeight
#print axioms HypercubicDimension16WilsonTraceOrderInvariantEOM.ourEOMZero_signedPlanePairWeight
#print axioms HypercubicDimension16WilsonTraceOrderInvariantEOM.ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero
#print axioms HypercubicDimension16WilsonTraceOrderInvariantEOM.ourInvariantEOMRow_mem
#print axioms HypercubicDimension16WilsonTraceOrderInvariantEOM.ourTwoCoordinateInvariantTraceOrderCorrection_invariantEOM_zero

end YangMills
end QuantumTheory
end Mettapedia
