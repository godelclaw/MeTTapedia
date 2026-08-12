import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_00
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_01
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_02
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_03
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_04
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_05
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_06

/-!
# OUR assembled incoming trace-coordinate replay block

The block exposes the same seven-coordinate interface while independently
compiled atomic facts retain the exact finite arithmetic certificates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16IncomingCommutatorTraceCoordinateCore

def assignmentIndex (localIndex : Fin 7) : Fin 98 :=
  ⟨77 + localIndex.1, by omega⟩

theorem replay :
    ∀ localIndex : Fin 7,
      literalIncomingUnsignedEvaluation (assignmentIndex localIndex) =
        (expectedUnsignedEvaluation (assignmentIndex localIndex) ⟨6, by decide⟩ -
          expectedUnsignedEvaluation (assignmentIndex localIndex) ⟨4, by decide⟩) / 4 := by
  intro localIndex
  fin_cases localIndex
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_00.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_01.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_02.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_03.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_04.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_05.replay_first
  · simpa only [assignmentIndex] using
      HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf011_06.replay_first

#print axioms replay

end HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011
end YangMills
end QuantumTheory
end Mettapedia
