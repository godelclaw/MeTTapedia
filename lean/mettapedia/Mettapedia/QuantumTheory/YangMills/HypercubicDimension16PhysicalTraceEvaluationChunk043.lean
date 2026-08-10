import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationBlock043_012

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceEvaluationChunk043

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16PhysicalTraceEvaluationSemantics
open HypercubicDimension16PhysicalTraceConditioningExecutable

def assignmentIndex (localIndex : Fin 2) : Fin 98 :=
  ⟨86 + localIndex.1, by omega⟩

def columnIndex000 (localIndex : Fin 8) : Fin 98 :=
  ⟨0 + localIndex.1, by omega⟩

def columnIndex001 (localIndex : Fin 8) : Fin 98 :=
  ⟨8 + localIndex.1, by omega⟩

def columnIndex002 (localIndex : Fin 8) : Fin 98 :=
  ⟨16 + localIndex.1, by omega⟩

def columnIndex003 (localIndex : Fin 8) : Fin 98 :=
  ⟨24 + localIndex.1, by omega⟩

def columnIndex004 (localIndex : Fin 8) : Fin 98 :=
  ⟨32 + localIndex.1, by omega⟩

def columnIndex005 (localIndex : Fin 8) : Fin 98 :=
  ⟨40 + localIndex.1, by omega⟩

def columnIndex006 (localIndex : Fin 8) : Fin 98 :=
  ⟨48 + localIndex.1, by omega⟩

def columnIndex007 (localIndex : Fin 8) : Fin 98 :=
  ⟨56 + localIndex.1, by omega⟩

def columnIndex008 (localIndex : Fin 8) : Fin 98 :=
  ⟨64 + localIndex.1, by omega⟩

def columnIndex009 (localIndex : Fin 8) : Fin 98 :=
  ⟨72 + localIndex.1, by omega⟩

def columnIndex010 (localIndex : Fin 8) : Fin 98 :=
  ⟨80 + localIndex.1, by omega⟩

def columnIndex011 (localIndex : Fin 8) : Fin 98 :=
  ⟨88 + localIndex.1, by omega⟩

def columnIndex012 (localIndex : Fin 2) : Fin 98 :=
  ⟨96 + localIndex.1, by omega⟩

/-- Assembly of the bounded unsigned evaluation replays. -/
theorem chunk_unsigned_evaluations :
    ∀ localIndex : Fin 2, ∀ freeIndex : Fin 98,
      fourPairUnsignedReynoldsEvaluation
          (assignmentIndex localIndex) freeIndex =
        expectedUnsignedEvaluation (assignmentIndex localIndex) freeIndex := by
  intro localIndex freeIndex
  by_cases hcolumn000 : freeIndex.1 < 8
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 0, by omega⟩
    have hequal : columnIndex000 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex000, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_000.unsigned localIndex columnLocalIndex
  by_cases hcolumn001 : freeIndex.1 < 16
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 8, by omega⟩
    have hequal : columnIndex001 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex001, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_001.unsigned localIndex columnLocalIndex
  by_cases hcolumn002 : freeIndex.1 < 24
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 16, by omega⟩
    have hequal : columnIndex002 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex002, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_002.unsigned localIndex columnLocalIndex
  by_cases hcolumn003 : freeIndex.1 < 32
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 24, by omega⟩
    have hequal : columnIndex003 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex003, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_003.unsigned localIndex columnLocalIndex
  by_cases hcolumn004 : freeIndex.1 < 40
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 32, by omega⟩
    have hequal : columnIndex004 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex004, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_004.unsigned localIndex columnLocalIndex
  by_cases hcolumn005 : freeIndex.1 < 48
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 40, by omega⟩
    have hequal : columnIndex005 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex005, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_005.unsigned localIndex columnLocalIndex
  by_cases hcolumn006 : freeIndex.1 < 56
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 48, by omega⟩
    have hequal : columnIndex006 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex006, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_006.unsigned localIndex columnLocalIndex
  by_cases hcolumn007 : freeIndex.1 < 64
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 56, by omega⟩
    have hequal : columnIndex007 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex007, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_007.unsigned localIndex columnLocalIndex
  by_cases hcolumn008 : freeIndex.1 < 72
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 64, by omega⟩
    have hequal : columnIndex008 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex008, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_008.unsigned localIndex columnLocalIndex
  by_cases hcolumn009 : freeIndex.1 < 80
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 72, by omega⟩
    have hequal : columnIndex009 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex009, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_009.unsigned localIndex columnLocalIndex
  by_cases hcolumn010 : freeIndex.1 < 88
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 80, by omega⟩
    have hequal : columnIndex010 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex010, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_010.unsigned localIndex columnLocalIndex
  by_cases hcolumn011 : freeIndex.1 < 96
  · let columnLocalIndex : Fin 8 := ⟨freeIndex.1 - 88, by omega⟩
    have hequal : columnIndex011 columnLocalIndex = freeIndex := by
      apply Fin.ext
      simp [columnIndex011, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_011.unsigned localIndex columnLocalIndex
  let columnLocalIndex : Fin 2 := ⟨freeIndex.1 - 96, by have := freeIndex.isLt; omega⟩
  have hequal : columnIndex012 columnLocalIndex = freeIndex := by
    apply Fin.ext
    simp [columnIndex012, columnLocalIndex] <;> omega
  rw [← hequal]
  exact HypercubicDimension16PhysicalTraceEvaluationBlock043_012.unsigned localIndex columnLocalIndex

/-- Assembly of the bounded exact inverse replays. -/
theorem chunk_evaluation_inverse :
    ∀ localIndex : Fin 2, ∀ column : Fin 98,
      (∑ middle : Fin 98,
        decodedEvaluationInverse (assignmentIndex localIndex) middle *
          expectedUnsignedEvaluation middle column) =
        if assignmentIndex localIndex = column then 1 else 0 := by
  intro localIndex column
  by_cases hcolumn000 : column.1 < 8
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 0, by omega⟩
    have hequal : columnIndex000 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex000, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_000.inverse localIndex columnLocalIndex
  by_cases hcolumn001 : column.1 < 16
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 8, by omega⟩
    have hequal : columnIndex001 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex001, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_001.inverse localIndex columnLocalIndex
  by_cases hcolumn002 : column.1 < 24
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 16, by omega⟩
    have hequal : columnIndex002 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex002, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_002.inverse localIndex columnLocalIndex
  by_cases hcolumn003 : column.1 < 32
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 24, by omega⟩
    have hequal : columnIndex003 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex003, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_003.inverse localIndex columnLocalIndex
  by_cases hcolumn004 : column.1 < 40
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 32, by omega⟩
    have hequal : columnIndex004 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex004, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_004.inverse localIndex columnLocalIndex
  by_cases hcolumn005 : column.1 < 48
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 40, by omega⟩
    have hequal : columnIndex005 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex005, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_005.inverse localIndex columnLocalIndex
  by_cases hcolumn006 : column.1 < 56
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 48, by omega⟩
    have hequal : columnIndex006 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex006, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_006.inverse localIndex columnLocalIndex
  by_cases hcolumn007 : column.1 < 64
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 56, by omega⟩
    have hequal : columnIndex007 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex007, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_007.inverse localIndex columnLocalIndex
  by_cases hcolumn008 : column.1 < 72
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 64, by omega⟩
    have hequal : columnIndex008 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex008, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_008.inverse localIndex columnLocalIndex
  by_cases hcolumn009 : column.1 < 80
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 72, by omega⟩
    have hequal : columnIndex009 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex009, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_009.inverse localIndex columnLocalIndex
  by_cases hcolumn010 : column.1 < 88
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 80, by omega⟩
    have hequal : columnIndex010 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex010, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_010.inverse localIndex columnLocalIndex
  by_cases hcolumn011 : column.1 < 96
  · let columnLocalIndex : Fin 8 := ⟨column.1 - 88, by omega⟩
    have hequal : columnIndex011 columnLocalIndex = column := by
      apply Fin.ext
      simp [columnIndex011, columnLocalIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceEvaluationBlock043_011.inverse localIndex columnLocalIndex
  let columnLocalIndex : Fin 2 := ⟨column.1 - 96, by have := column.isLt; omega⟩
  have hequal : columnIndex012 columnLocalIndex = column := by
    apply Fin.ext
    simp [columnIndex012, columnLocalIndex] <;> omega
  rw [← hequal]
  exact HypercubicDimension16PhysicalTraceEvaluationBlock043_012.inverse localIndex columnLocalIndex

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

end HypercubicDimension16PhysicalTraceEvaluationChunk043
end YangMills
end QuantumTheory
end Mettapedia
