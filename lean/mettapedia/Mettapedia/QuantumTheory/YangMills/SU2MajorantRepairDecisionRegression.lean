import Mettapedia.QuantumTheory.YangMills.SU2MajorantRepairDecision

/-!
# Regressions for the `SU(2)` coefficient-majorant decision
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2MajorantRepairDecisionRegression

open SU2CayleyHamiltonTruncationObstruction
open SU2MajorantRepairDecision

example : Fintype.card DecisionField = 16 := decisionField_count
example : decisionMatrix.length = 16 := decisionMatrix_length
example : ¬ TraceCanonicalTruncationDescends := descendedExtraction_obstructed
example : ¬ HasCompletedMajorantConstantLedger :=
  no_completedMajorantConstantLedger

#print axioms effectiveBlockAction_is_log_internalHaarIntegral
#print axioms effectiveBlockAction_zero
#print axioms blockPlaquette_unionRecombination_le
#print axioms no_completedMajorantConstantLedger
#print axioms decisionField_count
#print axioms decisionMatrix_length
#print axioms decisionMatrix_agrees_with_status
#print axioms filtrationCompatibility_obstructed
#print axioms descendedExtraction_obstructed
#print axioms su2MajorantRepairDecision_sealed

end SU2MajorantRepairDecisionRegression
end YangMills
end QuantumTheory
end Mettapedia
