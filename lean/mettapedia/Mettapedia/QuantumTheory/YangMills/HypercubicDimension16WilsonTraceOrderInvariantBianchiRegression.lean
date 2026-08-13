import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi

/-! Regression checks for OUR invariant Bianchi trace-order test. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi

example (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero policy

example (policy : PhysicalRelationPolicy) :
    ourInvariantBianchiRow policy ∈ jointInvariantRelationSubmodule policy :=
  ourInvariantBianchiRow_mem policy

example (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero policy

#print axioms HypercubicDimension16WilsonTraceOrderInvariantBianchi.ourBianchiBase_signedAxisWeight
#print axioms HypercubicDimension16WilsonTraceOrderInvariantBianchi.ourBianchiBase_signedPlanePairWeight
#print axioms HypercubicDimension16WilsonTraceOrderInvariantBianchi.ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms HypercubicDimension16WilsonTraceOrderInvariantBianchi.ourInvariantBianchiRow_mem
#print axioms HypercubicDimension16WilsonTraceOrderInvariantBianchi.ourTwoCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero

end YangMills
end QuantumTheory
end Mettapedia
