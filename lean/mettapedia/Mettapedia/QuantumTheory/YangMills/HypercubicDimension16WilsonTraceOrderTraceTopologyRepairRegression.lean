import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceTopologyRepair

/-! Regression checks for OUR trace-topology fourth-coordinate repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourCommutator_zero policy

example :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourIBP_zero

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourBianchi_zero policy

example :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourEOM_zero

example (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    policy generator

#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourEOM_zero
#print axioms HypercubicDimension16WilsonTraceOrderTraceTopologyRepair.ourFourCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero

end YangMills
end QuantumTheory
end Mettapedia
