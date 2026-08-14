import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility

/-!
# Regression for OUR two-class source-seven compatibility audit

The public interface replays the two commutator rows, retained rows, and the
exact nonzero second-IBP mismatch.  The latter is a deliberate obstruction
certificate, not a failed zero assertion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibilityRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example : ourSecondarySourceSevenResidual ≠ 0 :=
  ourSecondarySourceSevenResidual_ne_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_zero
    policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ≠ 0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
    policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example : ourAugmentedCycleProfileInvariantTraceOrderCorrection
    (orbitPhysicalRelationOperator .offShell
      (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourIBP_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    policy

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    policy generator

#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility.ourSecondarySourceSevenResidual_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility.ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility.ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibilityRegression
