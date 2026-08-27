import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_00
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_01
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_02
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_03

/-!
# OUR assembled incoming trace-coordinate replay block

The block exposes the same seven-coordinate interface while its four
independent atomic facts retain the exact finite arithmetic certificates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16IncomingCommutatorTraceCoordinateCore

def assignmentIndex (localIndex : Fin 7) : Fin 98 :=
  ⟨28 + localIndex.1, by omega⟩

theorem replay :
    ∀ localIndex : Fin 7,
      literalIncomingUnsignedEvaluation (assignmentIndex localIndex) =
        (expectedUnsignedEvaluation (assignmentIndex localIndex) ⟨6, by decide⟩ -
          expectedUnsignedEvaluation (assignmentIndex localIndex) ⟨4, by decide⟩) / 4 := by
  intro localIndex
  fin_cases localIndex
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_00.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_00.replay_second
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_01.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_01.replay_second
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_02.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_02.replay_second
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf004_03.replay_first

#print axioms replay

end HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004
end YangMills
end QuantumTheory
end Mettapedia
