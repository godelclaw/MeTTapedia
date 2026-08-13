import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantRepair

/-! Regression checks for OUR invariant two-coordinate trace-order repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair

example (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero policy

example :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero

example (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) = 0 :=
  ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    policy generator

example :
    ourInvariantIBPRow ∈ jointInvariantRelationSubmodule .offShell :=
  ourInvariantIBPRow_mem

#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.derivativeAxisPlanePairMultiplicity_relabel
#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.ourIBPAxisPlanePairSignedWeight
#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms HypercubicDimension16WilsonTraceOrderInvariantRepair.ourInvariantIBPRow_mem

end YangMills
end QuantumTheory
end Mettapedia
