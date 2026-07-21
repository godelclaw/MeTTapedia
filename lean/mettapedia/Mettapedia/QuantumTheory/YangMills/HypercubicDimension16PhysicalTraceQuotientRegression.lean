import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTracePublicConditioning
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceEvaluationBootstrap
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CovariantCompressionWall

/-!
# Regression checks for the derivative-free eight-field standard trace quotient
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceQuotientRegression

open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16PhysicalTracePublicConditioning
open HypercubicDimension16TraceEvaluationBootstrap
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16CovariantCompressionWall

example : Module.finrank ℚ FieldEightPhysicalTraceQuotient = 98 :=
  physicalTraceQuotient_finrank

example :
    publicEvaluationInverseRowL1 ⟨30, by decide⟩ =
      publicEvaluationConditioningConstant :=
  publicEvaluationInverseRowL1_attained

example :
    HasExtendedExtractionContraction
      traceEvaluationConditionedLedgerConstant 2 32 :=
  traceEvaluationConditioned_contraction_two_thirtyTwo

example :
    HasTwoSourceBootstrapSlack
      traceEvaluationConditionedLedgerConstant 2 34 :=
  traceEvaluationConditioned_twoSourceSlack_two_thirtyFour

example :
    fieldEightIncomingCommutatorReynolds ≠ 0 :=
  fieldEightIncomingCommutatorReynolds_ne_zero

example (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (fieldSevenCommutatorGenerator policy) 1)) ≠ 0 :=
  orbitPhysicalRelationOperator_nonzero_seven_to_eight policy

#print axioms physicalTraceRelationSubmodule_finrank
#print axioms physicalTraceQuotient_finrank
#print axioms physicalTraceCoefficientDual_freeClass
#print axioms publicEvaluationInverseRowL1_attained
#print axioms traceEvaluationConditioned_leastContractionDepth
#print axioms traceEvaluationConditioned_leastTwoSourceDepth
#print axioms exactDimension16ScalarInvariantDimension_total
#print axioms commutatorBeforeCoordinate_valid
#print axioms commutatorInsertionOrbit_before_eq
#print axioms orbitPhysicalRelationOperator_commutator_fieldEight
#print axioms fieldEightIncomingCommutatorReynolds_ne_zero
#print axioms orbitPhysicalRelationOperator_not_fieldCountBlockDiagonal

end HypercubicDimension16PhysicalTraceQuotientRegression
end YangMills
end QuantumTheory
end Mettapedia
