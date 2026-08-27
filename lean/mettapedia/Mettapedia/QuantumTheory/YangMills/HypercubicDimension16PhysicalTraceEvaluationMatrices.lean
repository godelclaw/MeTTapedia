import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationData
import Mettapedia.QuantumTheory.YangMills.SU2LatticeFDCensusNoGo
import Mathlib.Data.Matrix.Basic

/-!
# Matrix assignments for the eight-field trace evaluations

This small interface exposes the finite rational matrix library independently
of the orbit-chart evaluator.  Trace-relation arguments need only these
assignments and therefore do not import representative-chart payloads.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationMatrices

open HypercubicDimension16PhysicalTraceEvaluationData
open SU2LatticeFDCensusNoGo

/-- Decode one stored rational `2 × 2` matrix. -/
@[reducible] def encodedMatrix (code : Array Int) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  fun row column => (code.getD (2 * row.1 + column.1) 0 : ℚ)

/-- The matrix assigned to one oriented plane in one stored evaluation. -/
@[reducible] def encodedEvaluationMatrixAt
    (assignment : Fin 98) (plane : OrientedPlane) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  let assignmentCode := evaluationAssignments.getD assignment.1 #[]
  let libraryIndex := assignmentCode.getD plane.1 0
  encodedMatrix (matrixLibrary.getD libraryIndex #[])

end HypercubicDimension16PhysicalTraceEvaluationMatrices
end YangMills
end QuantumTheory
end Mettapedia
