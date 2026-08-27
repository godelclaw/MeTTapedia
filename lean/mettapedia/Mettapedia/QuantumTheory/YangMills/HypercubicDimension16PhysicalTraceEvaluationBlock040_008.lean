import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationTraceCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceConditioningExecutable

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationBlock040_008

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTraceEvaluationSemantics
open HypercubicDimension16PhysicalTraceConditioningExecutable

def assignmentIndex (localIndex : Fin 2) : Fin 98 :=
  ⟨80 + localIndex.1, by omega⟩

def columnIndex (localIndex : Fin 8) : Fin 98 :=
  ⟨64 + localIndex.1, by omega⟩

/-- Kernel replay of one bounded unsigned evaluation block. -/
theorem unsigned :
    ∀ assignmentLocalIndex : Fin 2, ∀ columnLocalIndex : Fin 8,
      fourPairUnsignedReynoldsEvaluation
          (assignmentIndex assignmentLocalIndex) (columnIndex columnLocalIndex) =
        expectedUnsignedEvaluation (assignmentIndex assignmentLocalIndex) (columnIndex columnLocalIndex) := by
  decide +kernel

/-- Kernel replay of one bounded inverse block. -/
theorem inverse :
    ∀ assignmentLocalIndex : Fin 2, ∀ columnLocalIndex : Fin 8,
      (∑ middle : Fin 98,
        decodedEvaluationInverse (assignmentIndex assignmentLocalIndex) middle *
          expectedUnsignedEvaluation middle (columnIndex columnLocalIndex)) =
        if assignmentIndex assignmentLocalIndex = columnIndex columnLocalIndex then 1 else 0 := by
  decide +kernel

end HypercubicDimension16PhysicalTraceEvaluationBlock040_008
end YangMills
end QuantumTheory
end Mettapedia
