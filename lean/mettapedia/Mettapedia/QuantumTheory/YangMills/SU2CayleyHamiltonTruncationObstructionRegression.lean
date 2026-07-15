import Mettapedia.QuantumTheory.YangMills.SU2CayleyHamiltonTruncationObstruction

/-!
# Regressions for the intrinsic `SU(2)` trace-word truncation obstruction
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2CayleyHamiltonTruncationObstructionRegression

open SU2CayleyHamiltonTruncationObstruction

example : ¬ TraceCanonicalTruncationDescends :=
  cayleyHamiltonTruncation_does_not_descend

example :
    evaluateTraceRelationCoefficients
        (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients)
        SU2CanonicalTruncationObstruction.witnessField
        (SU2CanonicalTruncationObstruction.profilePlaquette 1) = -32 :=
  truncatedCayleyHamiltonRelation_witness

#print axioms trace_square_eq_trace_sq_sub_two_det
#print axioms centeredDoubleTrace_eq
#print axioms centeredTrace_conjugation
#print axioms centeredDoubleTrace_conjugation
#print axioms plaquetteCenteredTrace_gaugeAct
#print axioms plaquetteCenteredDoubleTrace_gaugeAct
#print axioms traceRelationCanonicalDimensions
#print axioms evaluateTraceRelationMonomial_gaugeAct
#print axioms evaluate_cayleyHamiltonRelation
#print axioms evaluate_truncatedCayleyHamiltonRelation
#print axioms cayleyHamiltonRelation_semantically_zero
#print axioms truncatedCayleyHamiltonRelation_witness
#print axioms truncatedCayleyHamiltonRelation_not_semantically_zero
#print axioms cayleyHamiltonTruncation_does_not_descend
#print axioms traceSemanticKernel_not_stable_under_truncation

end SU2CayleyHamiltonTruncationObstructionRegression
end YangMills
end QuantumTheory
end Mettapedia
