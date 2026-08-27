import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# Regression for OUR singleton-trace three-class refutation

The regression records the exact nonzero value on the actual source-seven
tracelessness relation for each physical relation policy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutationRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) =
      (-1 / 10 : ℚ) • literalIncomingCommutatorClass :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace policy

example (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) ≠ 0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace_ne_zero policy

example :
    physicalRelationGeneratorSourceFieldCount
      (ourSingletonTraceGenerator .offShell) = ourSevenFieldCount :=
  ourSingletonTrace_sourceFieldCount

example (policy : PhysicalRelationPolicy)
    (incomingValue secondaryValue thirdValue : FieldEightPhysicalTraceQuotient) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker
        (ourThreeSelectorSourceSevenExtension
          incomingValue secondaryValue thirdValue) :=
  ourThreeSelectorSourceSevenExtension_not_descends
    policy incomingValue secondaryValue thirdValue

#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation.ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation.ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace_ne_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation.ourThreeSelectorSourceSevenExtension_not_descends

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutationRegression
