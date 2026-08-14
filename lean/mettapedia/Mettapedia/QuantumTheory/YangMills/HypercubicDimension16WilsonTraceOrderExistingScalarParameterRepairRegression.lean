import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation

/-!
# Regression for OUR existing-scalar singleton repair candidate

The regression records both sides of the finite audit: the signed-invariant
existing-coordinate deformation cancels several named rows, while a second
actual singleton-trace row refutes its descent through the full physical
relation submodule.
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
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation

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

set_option maxRecDepth 100000 in
example (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondIBPSingletonTraceGenerator policy) 1)) ≠ 0 :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBPSingletonTrace_ne_zero
    policy

set_option maxRecDepth 100000 in
example (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker ourParameterSynthesizedSourceSevenTraceOrderCorrection :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_not_descends policy

#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation.ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBPSingletonTrace_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation.ourParameterSynthesizedSourceSevenTraceOrderCorrection_not_descends

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairRegression
