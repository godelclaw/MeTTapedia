import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinates

/-!
# OUR merged dual-row conditioning calculation

The exact coordinate identity for the bounded incoming class makes the sum
of the fourth and sixth standard coefficient duals the distinguished
candidate that annihilates that class.  This file records the exact public
row-`l1` cost of that merged row.  Its descent to the augmented quotient is
established separately; no conditioning claim about the complete physical
quotient is made here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceConditioning

open HypercubicDimension16PhysicalTracePublicConditioning

/-- OUR public evaluation row obtained by merging the fourth and sixth
standard coefficient duals. -/
def mergedPublicEvaluationInverse (assignment : Fin 98) : ℚ :=
  publicEvaluationInverse ⟨4, by decide⟩ assignment +
    publicEvaluationInverse ⟨6, by decide⟩ assignment

/-- OUR coefficient-sup analysis cost of the merged public dual row. -/
def mergedPublicEvaluationInverseRowL1 : ℚ :=
  ∑ assignment : Fin 98, |mergedPublicEvaluationInverse assignment|

/- Kernel-checked exact row-`l1` cost of OUR merged dual row. -/
set_option maxHeartbeats 3000000 in
theorem mergedPublicEvaluationInverseRowL1_exact :
    mergedPublicEvaluationInverseRowL1 = 367884889 / 10784 := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-- OUR merged row is bounded by the already certified sharp standard
coefficient-sup constant. -/
theorem mergedPublicEvaluationInverseRowL1_le_existing :
    mergedPublicEvaluationInverseRowL1 ≤
      publicEvaluationConditioningConstant := by
  rw [mergedPublicEvaluationInverseRowL1_exact]
  norm_num [publicEvaluationConditioningConstant]

#print axioms mergedPublicEvaluationInverseRowL1_exact
#print axioms mergedPublicEvaluationInverseRowL1_le_existing

end HypercubicDimension16IncomingCommutatorTraceConditioning
end YangMills
end QuantumTheory
end Mettapedia
