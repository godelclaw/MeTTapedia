import Mettapedia.Algebra.SupportTensor
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop

/-!
# Compressed-row realization of support-aware tensors

Rows are packed into a flat payload and an independently computed pointer
table. Decoding uses pointer subtraction and slicing, not the source rows.
Grouping a COO occurrence stream into rows preserves its first-occurrence
lookup, including explicit zeroes. Transposing before the same construction
gives the corresponding compressed-column realization.

These are representation/algorithm laws. They do not identify a list model
with a native buffer implementation or assert IEEE reassociation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensorLayout

open SupportTensor

variable {A R : Type*}

def offset : List (List A) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | row :: rest, i + 1 => row.length + offset rest i

structure PackedRows (A : Type*) where
  pointers : List Nat
  payload : List A
  deriving Repr

def packRows (rows : List (List A)) : PackedRows A :=
  ⟨(List.range (rows.length + 1)).map (offset rows), rows.flatten⟩

def segment (packed : PackedRows A) (row : Nat) : List A :=
  let first := packed.pointers[row]?.getD 0
  let last := packed.pointers[row+1]?.getD 0
  (packed.payload.drop first).take (last - first)

theorem packed_pointer (rows : List (List A)) (i : Nat) (valid : i ≤ rows.length) :
    (packRows rows).pointers[i]? = some (offset rows i) := by
  simp [packRows, List.getElem?_map, List.getElem?_range (by omega : i < rows.length+1)]

theorem offset_zero (rows : List (List A)) : offset rows 0 = 0 := by
  cases rows <;> rfl

theorem offset_end (rows : List (List A)) : offset rows rows.length = rows.flatten.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simpa [offset] using congrArg (row.length + ·) ih

theorem offset_step (rows : List (List A)) (i : Nat) (valid : i < rows.length) :
    offset rows (i+1) = offset rows i + (rows[i]?.getD []).length := by
  induction rows generalizing i with
  | nil => simp at valid
  | cons row rest ih =>
      cases i with
      | zero => simp [offset, offset_zero]
      | succ i =>
          have := ih i (by simpa using valid)
          simpa [offset, Nat.add_assoc] using congrArg (row.length + ·) this

private theorem payload_slice (rows : List (List A)) (i : Nat) (valid : i < rows.length) :
    (rows.flatten.drop (offset rows i)).take
      (offset rows (i+1)-offset rows i) = rows[i]?.getD [] := by
  induction rows generalizing i with
  | nil => simp at valid
  | cons row rest ih =>
      cases i with
      | zero => simp [offset, offset_zero]
      | succ i =>
          have hi : i < rest.length := by simpa using valid
          simpa [offset, ← List.drop_drop, Nat.add_sub_add_left] using ih i hi

theorem segment_packRows (rows : List (List A)) (i : Nat) (valid : i < rows.length) :
    segment (packRows rows) i = rows[i]?.getD [] := by
  unfold segment
  rw [packed_pointer rows i (by omega), packed_pointer rows (i+1) (by omega)]
  simpa [packRows] using payload_slice rows i valid

theorem pointer_table_size (rows : List (List A)) :
    (packRows rows).pointers.length = rows.length+1 := by simp [packRows]

theorem pointer_table_end (rows : List (List A)) :
    (packRows rows).pointers[rows.length]? = some (packRows rows).payload.length := by
  rw [packed_pointer rows rows.length (by omega), offset_end]
  rfl

def rowEntries {m n : Nat} (entries : List ((Fin m × Fin n) × R))
    (row : Fin m) : List (Fin n × R) :=
  entries.filterMap fun entry => if entry.1.1 = row then some (entry.1.2,entry.2) else none

def compress {m n : Nat} (entries : List ((Fin m × Fin n) × R)) : PackedRows (Fin n × R) :=
  packRows ((List.finRange m).map (rowEntries entries))

def decode {m n : Nat} (packed : PackedRows (Fin n × R)) : Value (Fin m × Fin n) R :=
  fun coordinate => lookupFirst (segment packed coordinate.1.val) coordinate.2

theorem row_lookup {m n : Nat} (entries : List ((Fin m × Fin n) × R))
    (row : Fin m) (col : Fin n) :
    lookupFirst (rowEntries entries row) col = lookupFirst entries (row,col) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨⟨r,c⟩,value⟩
      by_cases hr : r = row
      · subst r
        by_cases hc : c = col
        · subst c; simp [rowEntries, lookupFirst]
        · simpa [rowEntries, lookupFirst, hc] using ih
      · simpa [rowEntries, lookupFirst, hr] using ih

theorem compress_preserves_support {m n : Nat}
    (entries : List ((Fin m × Fin n) × R)) :
    decode (compress entries) = lookupFirst entries := by
  funext coordinate
  rcases coordinate with ⟨row,col⟩
  unfold decode compress
  rw [segment_packRows _ row.val (by simp)]
  simpa using row_lookup entries row col

/-- The filled numerical observation alone is weaker; the representation law
above preserves the complete Option-valued observation. -/
theorem compress_preserves_fill {m n : Nat} (default : R)
    (entries : List ((Fin m × Fin n) × R)) :
    fill default (decode (compress entries)) = fill default (lookupFirst entries) := by
  rw [compress_preserves_support]

def transposeEntries {m n : Nat} (entries : List ((Fin m × Fin n) × R)) :
    List ((Fin n × Fin m) × R) := entries.map fun entry => ((entry.1.2,entry.1.1),entry.2)

theorem transpose_lookup {m n : Nat} (entries : List ((Fin m × Fin n) × R))
    (row : Fin m) (col : Fin n) :
    lookupFirst (transposeEntries entries) (col,row) = lookupFirst entries (row,col) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨⟨r,c⟩,value⟩
      by_cases hr : r = row <;> by_cases hc : c = col <;>
        simp_all [transposeEntries, lookupFirst]

theorem compress_columns_preserves_support {m n : Nat}
    (entries : List ((Fin m × Fin n) × R)) (row : Fin m) (col : Fin n) :
    decode (compress (transposeEntries entries)) (col,row) = lookupFirst entries (row,col) := by
  rw [compress_preserves_support, transpose_lookup]

example : segment (packRows ([[], [4,0], [], [7]] : List (List Nat))) 1 = [4,0] := by decide
example : segment (packRows ([[], [4,0], [], [7]] : List (List Nat))) 2 = [] := by decide
example : segment (⟨[0,1], [4,0]⟩ : PackedRows Nat) 0 ≠ [4,0] := by decide

#print axioms compress_preserves_support
#print axioms compress_columns_preserves_support

end Mettapedia.Algebra.SupportTensorLayout
