import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationTraceCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceConditioningExecutable

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationChunk025

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTraceEvaluationSemantics
open HypercubicDimension16PhysicalTraceConditioningExecutable

def assignmentIndex (localIndex : Fin 2) : Fin 98 :=
  ⟨50 + localIndex.1, by omega⟩

/-- Kernel replay of the exact unsigned evaluation rows in this range. -/
theorem chunk_unsigned_evaluations :
    ∀ localIndex : Fin 2, ∀ freeIndex : Fin 98,
      fourPairUnsignedReynoldsEvaluation
          (assignmentIndex localIndex) freeIndex =
        expectedUnsignedEvaluation (assignmentIndex localIndex) freeIndex := by
  decide +kernel

/-- Rational left-inverse replay for the same row range. -/
theorem chunk_evaluation_inverse :
    ∀ localIndex : Fin 2, ∀ column : Fin 98,
      (∑ middle : Fin 98,
        decodedEvaluationInverse (assignmentIndex localIndex) middle *
          expectedUnsignedEvaluation middle column) =
        if assignmentIndex localIndex = column then 1 else 0 := by
  decide +kernel

/-- Exact-fraction fold replay of the row-l1 data in this range. -/
theorem chunk_inverse_row_l1_replay :
    ∀ localIndex : Fin 2,
      EncodedInverseRowL1ReplayValid
        (assignmentIndex localIndex) := by
  decide +kernel

/-- Integer cross-multiplication bounds for the same rows. -/
theorem chunk_inverse_row_l1_bound :
    ∀ localIndex : Fin 2,
      EncodedInverseRowL1Bound (assignmentIndex localIndex) := by
  decide +kernel

end HypercubicDimension16PhysicalTraceEvaluationChunk025
end YangMills
end QuantumTheory
end Mettapedia
