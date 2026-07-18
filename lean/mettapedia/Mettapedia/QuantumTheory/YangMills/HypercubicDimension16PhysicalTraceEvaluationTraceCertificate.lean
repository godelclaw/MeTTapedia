import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationSemantics

/-! # Checked trace shape of the 98 free physical columns -/

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationTraceCertificate

open HypercubicDimension16PhysicalTraceEvaluationSemantics

/-- Every certified free column has trace partition `(2,2,2,2)`, with the
stored labels paired as `(0,1)`, `(2,3)`, `(4,5)`, `(6,7)`. -/
theorem freeRepresentatives_have_fourPairTrace :
    ∀ freeIndex : Fin 98,
      FreeRepresentativeHasFourPairTrace freeIndex := by
  decide +kernel

#print axioms freeRepresentatives_have_fourPairTrace

end HypercubicDimension16PhysicalTraceEvaluationTraceCertificate
end YangMills
end QuantumTheory
end Mettapedia
