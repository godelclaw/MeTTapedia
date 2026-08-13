import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

/-! Regression checks for OUR fifth-coordinate fundamental-three-cut repair. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      (-1 / 2 : ℚ) •
        HypercubicDimension16IncomingCommutatorTraceCertificate.literalIncomingCommutatorClass :=
  ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut policy

example (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 ≠ 0 :=
  ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_ne_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 :=
  ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 :=
  ourFiveCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero policy

example (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 :=
  ourFiveCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero policy

example (policy : PhysicalRelationPolicy) :
    ourInvariantFundamentalThreeCutRow policy ∈
      jointInvariantRelationSubmodule policy :=
  ourInvariantFundamentalThreeCutRow_mem policy

#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut
#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourFiveCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourFiveCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair.ourInvariantFundamentalThreeCutRow_mem

end YangMills
end QuantumTheory
end Mettapedia
