import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair

/-!
# Regression for OUR existing-scalar singleton repair candidate

The regression records the two exact checks completed for the signed-invariant
existing-coordinate deformation: it cancels the singleton mismatch and retains
the original incoming source-seven commutator.  It deliberately does not
represent a full source-seven descent claim.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair

set_option maxRecDepth 100000 in
example (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
    policy

set_option maxRecDepth 100000 in
example (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
    policy

set_option maxRecDepth 100000 in
example (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
        0 :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
    policy

#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairRegression
