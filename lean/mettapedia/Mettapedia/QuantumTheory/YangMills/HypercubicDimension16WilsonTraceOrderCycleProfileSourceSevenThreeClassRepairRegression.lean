import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair

/-!
# Regression for OUR three-class source-seven repair

The interface replays the two explicit source-seven commutators, the exact
second-IBP obstruction that defeated the two-class augmentation, and the
named retained differential and trace rows.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepairRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourCommutator_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_liftedTraceGenerator_zero
    policy generator

#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair.ourInvariantThirdIBPAxisCoordinate_ourSecondaryCommutator
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair.ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair.ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepairRegression
