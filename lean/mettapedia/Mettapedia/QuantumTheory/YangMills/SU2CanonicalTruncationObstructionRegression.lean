import Mettapedia.QuantumTheory.YangMills.SU2CanonicalTruncationObstruction

/-!
# Regressions for the `SU(2)` canonical-truncation obstruction
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2CanonicalTruncationObstructionRegression

open SU2CanonicalTruncationObstruction

example :
    ¬ CanonicalTruncationDescends :=
  canonicalTruncation_does_not_descend

example :
    ¬ (∀ c : DerivativeCoefficients,
      SemanticallyEquivalent c 0 →
        SemanticallyEquivalent (truncateThrough16 c) 0) :=
  semanticKernel_not_stable_under_truncation

example :
    evaluateCoefficients
        (truncateThrough16 orderFiveRelationCoefficients)
        (wilsonDensity12Profile witnessField) 0 = -5 :=
  truncatedRelation_nonzero_on_witness

#print axioms quarterTurn_trace_real
#print axioms witnessHolonomy_zero
#print axioms witnessHolonomy_one
#print axioms witness_wilsonDensity12Profile
#print axioms zeroBoundaryShift_sq
#print axioms order_five_relation
#print axioms witness_order_five_value
#print axioms evaluate_orderFiveRelation
#print axioms evaluate_truncated_orderFiveRelation
#print axioms orderFiveRelation_semantically_zero
#print axioms truncatedRelation_nonzero_on_witness
#print axioms truncatedRelation_not_semantically_zero
#print axioms canonicalTruncation_does_not_descend
#print axioms semanticKernel_not_stable_under_truncation

end SU2CanonicalTruncationObstructionRegression
end YangMills
end QuantumTheory
end Mettapedia
