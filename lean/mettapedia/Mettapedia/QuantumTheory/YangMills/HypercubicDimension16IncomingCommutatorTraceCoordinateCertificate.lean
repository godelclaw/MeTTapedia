import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock012
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateBlock013

/-!
# OUR bounded replay of the incoming trace-coordinate column

The finite replay is split into fourteen seven-assignment blocks.  Each block
checks only the literal incoming column; it does not duplicate the existing
`98 x 98` inverse certificate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoordinateCertificate

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16IncomingCommutatorTraceCoordinateCore

/-- The checked unsigned incoming column is one quarter of the difference of
the two certified free columns selected by its exact coordinate solve. -/
theorem literalIncomingUnsignedEvaluation_replay (assignment : Fin 98) :
    literalIncomingUnsignedEvaluation assignment =
      (expectedUnsignedEvaluation assignment ⟨6, by decide⟩ -
        expectedUnsignedEvaluation assignment ⟨4, by decide⟩) / 4 := by
  by_cases h000 : assignment.1 < 7
  · let localIndex : Fin 7 := ⟨assignment.1 - 0, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock000.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock000.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock000.replay localIndex
  by_cases h001 : assignment.1 < 14
  · let localIndex : Fin 7 := ⟨assignment.1 - 7, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock001.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock001.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock001.replay localIndex
  by_cases h002 : assignment.1 < 21
  · let localIndex : Fin 7 := ⟨assignment.1 - 14, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock002.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock002.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock002.replay localIndex
  by_cases h003 : assignment.1 < 28
  · let localIndex : Fin 7 := ⟨assignment.1 - 21, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock003.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock003.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock003.replay localIndex
  by_cases h004 : assignment.1 < 35
  · let localIndex : Fin 7 := ⟨assignment.1 - 28, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock004.replay localIndex
  by_cases h005 : assignment.1 < 42
  · let localIndex : Fin 7 := ⟨assignment.1 - 35, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock005.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock005.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock005.replay localIndex
  by_cases h006 : assignment.1 < 49
  · let localIndex : Fin 7 := ⟨assignment.1 - 42, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock006.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock006.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock006.replay localIndex
  by_cases h007 : assignment.1 < 56
  · let localIndex : Fin 7 := ⟨assignment.1 - 49, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock007.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock007.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock007.replay localIndex
  by_cases h008 : assignment.1 < 63
  · let localIndex : Fin 7 := ⟨assignment.1 - 56, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock008.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock008.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock008.replay localIndex
  by_cases h009 : assignment.1 < 70
  · let localIndex : Fin 7 := ⟨assignment.1 - 63, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock009.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock009.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock009.replay localIndex
  by_cases h010 : assignment.1 < 77
  · let localIndex : Fin 7 := ⟨assignment.1 - 70, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock010.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock010.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock010.replay localIndex
  by_cases h011 : assignment.1 < 84
  · let localIndex : Fin 7 := ⟨assignment.1 - 77, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock011.replay localIndex
  by_cases h012 : assignment.1 < 91
  · let localIndex : Fin 7 := ⟨assignment.1 - 84, by omega⟩
    have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock012.assignmentIndex localIndex = assignment := by
      apply Fin.ext
      simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock012.assignmentIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock012.replay localIndex
  let localIndex : Fin 7 :=
      ⟨assignment.1 - 91, by have := assignment.isLt; omega⟩
  have hequal : HypercubicDimension16IncomingCommutatorTraceCoordinateBlock013.assignmentIndex localIndex = assignment := by
    apply Fin.ext
    simp [HypercubicDimension16IncomingCommutatorTraceCoordinateBlock013.assignmentIndex, localIndex] <;> omega
  rw [← hequal]
  exact HypercubicDimension16IncomingCommutatorTraceCoordinateBlock013.replay localIndex

#print axioms literalIncomingUnsignedEvaluation_replay

end HypercubicDimension16IncomingCommutatorTraceCoordinateCertificate
end YangMills
end QuantumTheory
end Mettapedia
