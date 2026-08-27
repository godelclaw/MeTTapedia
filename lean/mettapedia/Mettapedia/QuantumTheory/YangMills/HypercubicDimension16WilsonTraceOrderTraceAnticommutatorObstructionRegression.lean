import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

/-! Regression checks for OUR canonical trace-anticommutator obstruction. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

example (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass :=
  ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator policy

example (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) ≠ 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_ne_zero
    policy

example (policy : PhysicalRelationPolicy) :
    ourInvariantTraceAnticommutatorRow policy ∈
      jointInvariantRelationSubmodule policy :=
  ourInvariantTraceAnticommutatorRow_mem policy

example (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 ≠ 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_ne_zero
    policy

example (policy : PhysicalRelationPolicy) :
    ¬ ∀ value : exactFieldOrbitInvariantSubmodule,
      value ∈ jointInvariantRelationSubmodule policy →
        ourThreeCoordinateInvariantTraceOrderCorrection value.1 = 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_not_annihilates_joint policy

#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.orbitPhysicalRelationOperator_ourTraceAnticommutator
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourInvariantSevenAxisCoordinate_ourTraceAnticommutator
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourInvariantIBPAxisCoordinate_ourTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourInvariantTraceAnticommutatorRow_mem
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction.ourThreeCoordinateInvariantTraceOrderCorrection_not_annihilates_joint

end YangMills
end QuantumTheory
end Mettapedia
