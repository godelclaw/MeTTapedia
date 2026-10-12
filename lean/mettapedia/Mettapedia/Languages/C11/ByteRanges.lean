import Mettapedia.Machines.CMemory.ExecutableStorage
import Mathlib.Data.List.OfFn

/-!
# Byte ranges over finite allocation storage

Addresses in this interface count bytes. A constructed adapter uses one
storage cell per byte and reuses the existing allocation identities,
liveness checks and ownership algebra. This does not identify byte offsets
with the scalar-object offsets of other CMemory instances.

Raw representation reads and writes retain indeterminate-byte markers.
They are memory operations below typed C accesses: effective types, trap
representations, character-read choices, volatile observations and complete
object layout are additional layers. Copying a representation therefore
does not manufacture an initialized scalar value.

Finite list execution corresponds to independent byte-wise heap judgments.
Range writes preserve the allocation header and every byte outside the
range. Empty ranges still require a live allocation and an in-bounds or
one-past address; this kernel alone is not the C library argument contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ByteRanges

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open scoped Mettapedia.GSLT.SeparationAlgebra

namespace Storage

abbrev State (Byte : Type) := ExecutableStorage.Storage Byte

end Storage

structure Address where
  allocation : BlockId
  offset : Nat
  deriving DecidableEq, Repr

def Address.cell (address : Address) : Ptr := ⟨address.allocation, address.offset⟩

structure Range where
  address : Address
  extent : Nat
  deriving DecidableEq, Repr

def Range.Contains (range : Range) (offset : Nat) : Prop :=
  range.address.offset ≤ offset ∧ offset < range.address.offset + range.extent

instance (range : Range) (offset : Nat) : Decidable (range.Contains offset) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Range.Disjoint (left right : Range) : Prop :=
  left.extent = 0 ∨ right.extent = 0 ∨ left.address.allocation ≠ right.address.allocation ∨
    left.address.offset + left.extent ≤ right.address.offset ∨
    right.address.offset + right.extent ≤ left.address.offset

instance (left right : Range) : Decidable (left.Disjoint right) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

theorem Range.Disjoint.symm {left right : Range} (disjoint : left.Disjoint right) :
    right.Disjoint left := by
  rcases disjoint with emptyLeft | emptyRight | different | before | after
  · exact Or.inr (Or.inl emptyLeft)
  · exact Or.inl emptyRight
  · exact Or.inr (Or.inr (Or.inl different.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr before)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl after)))

theorem Range.Disjoint.excludes {left right : Range} (disjoint : left.Disjoint right)
    (same : left.address.allocation = right.address.allocation) (offset : Nat) :
    ¬ (left.Contains offset ∧ right.Contains offset) := by
  rcases disjoint with emptyLeft | emptyRight | different | before | after
  · simp only [Range.Contains]
    omega
  · simp only [Range.Contains]
    omega
  · exact fun _ => different same
  · simp only [Range.Contains]
    omega
  · simp only [Range.Contains]
    omega

variable {Byte : Type}

abbrev heap := @ExecutableStorage.heap Byte

def snapshot (cells : List (Option Byte)) (offset extent : Nat) : List (Option Byte) :=
  List.ofFn fun index : Fin extent => (cells[offset + index.val]?).getD none

@[simp]
theorem snapshot_length (cells : List (Option Byte)) (offset extent : Nat) :
    (snapshot cells offset extent).length = extent := by
  simp [snapshot]

theorem snapshot_byte (cells : List (Option Byte)) (offset extent index : Nat)
    (inside : index < extent) :
    ((snapshot cells offset extent)[index]?).getD none =
      (cells[offset + index]?).getD none := by
  simp [snapshot, inside]

def readBytes (storage : Storage.State Byte) (range : Range) : Option (List (Option Byte)) := do
  let block ← storage.lookup range.address.allocation
  if block.live ∧ range.address.offset + range.extent ≤ block.cells.length then
    some (snapshot block.cells range.address.offset range.extent)
  else none

/-- A byte-wise representation read, including owned indeterminate bytes. -/
def ReadRange (before : Heap (Excl (Option Byte))) (range : Range)
    (contents : List (Option Byte)) : Prop :=
  ∃ extent, (before range.address.allocation).1 = .own ⟨extent, true⟩ ∧
    range.address.offset + range.extent ≤ extent ∧ contents.length = range.extent ∧
    ∀ index < range.extent,
      read ((before range.address.allocation).2 (range.address.offset + index)) =
        some ((contents[index]?).getD none)

theorem readBytes_sound (storage : Storage.State Byte) (range : Range)
    (contents : List (Option Byte)) (executed : readBytes storage range = some contents) :
    ReadRange (heap storage) range contents := by
  cases present : storage.lookup range.address.allocation with
  | none => simp [readBytes, present] at executed
  | some block =>
      by_cases valid : block.live = true ∧ range.address.offset + range.extent ≤ block.cells.length
      · simp [readBytes, present, valid] at executed
        subst contents
        refine ⟨block.cells.length, ?_, valid.2, snapshot_length _ _ _, ?_⟩
        · simp [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
            ExecutableStorage.Block.header, valid.1]
        · intro index inside
          have bound : range.address.offset + index < block.cells.length := by omega
          simp [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
            valid.1, snapshot_byte _ _ _ _ inside, List.getElem?_eq_getElem bound]
      · simp [readBytes, present, valid] at executed

theorem readBytes_complete (storage : Storage.State Byte) (range : Range)
    (contents : List (Option Byte)) (readable : ReadRange (heap storage) range contents) :
    readBytes storage range = some contents := by
  obtain ⟨extent, header, bounds, length, bytes⟩ := readable
  cases present : storage.lookup range.address.allocation with
  | none => simp [heap, ExecutableStorage.heap, present, Excl.zero_def] at header
  | some block =>
      have fields : block.cells.length = extent ∧ block.live = true := by
        simpa [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
          ExecutableStorage.Block.header] using header
      have valid : range.address.offset + range.extent ≤ block.cells.length := by omega
      have contentEqual : snapshot block.cells range.address.offset range.extent = contents := by
        apply List.ext_getElem
        · simpa using length.symm
        · intro index first second
          have inside : index < range.extent := by simpa using first
          have cellBound : range.address.offset + index < block.cells.length := by omega
          have byte := bytes index inside
          simpa [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
            fields.2, List.getElem?_eq_getElem cellBound, List.getElem?_eq_getElem second,
            snapshot, List.getElem_ofFn] using byte
      simp [readBytes, present, fields.2, valid, contentEqual]

theorem readBytes_iff (storage : Storage.State Byte) (range : Range)
    (contents : List (Option Byte)) :
    readBytes storage range = some contents ↔ ReadRange (heap storage) range contents :=
  ⟨readBytes_sound storage range contents, readBytes_complete storage range contents⟩

def overwrite (cells : List (Option Byte)) (address : Address)
    (contents : List (Option Byte)) : List (Option Byte) :=
  List.ofFn fun index : Fin cells.length =>
    if address.offset ≤ index.val ∧ index.val < address.offset + contents.length then
      (contents[index.val - address.offset]?).getD none
    else cells[index.val]

@[simp]
theorem overwrite_length (cells : List (Option Byte)) (address : Address)
    (contents : List (Option Byte)) : (overwrite cells address contents).length = cells.length := by
  simp [overwrite]

def writeBytes (storage : Storage.State Byte) (address : Address)
    (contents : List (Option Byte)) : Option (Storage.State Byte) := do
  let block ← storage.lookup address.allocation
  if block.live ∧ address.offset + contents.length ≤ block.cells.length then
    some (ExecutableStorage.put storage address.allocation
      { block with cells := overwrite block.cells address contents })
  else none

/-- Logical byte updates use functions and permissions, independently of the
finite-list writer. -/
def updateRange (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) : Heap (Excl (Option Byte)) :=
  Function.update before address.allocation
    ((before address.allocation).1, fun offset =>
      if address.offset ≤ offset ∧ offset < address.offset + contents.length then
        whole ((contents[offset - address.offset]?).getD none)
      else (before address.allocation).2 offset)

theorem writeBytes_heap (storage : Storage.State Byte) (address : Address)
    (contents : List (Option Byte)) (block : ExecutableStorage.Block Byte)
    (present : storage.lookup address.allocation = some block) (live : block.live = true)
    (bounds : address.offset + contents.length ≤ block.cells.length) :
    heap (ExecutableStorage.put storage address.allocation
      { block with cells := overwrite block.cells address contents }) =
      updateRange (heap storage) address contents := by
  rw [heap, ExecutableStorage.heap_put]
  apply congrArg (Function.update (heap storage) address.allocation)
  apply blockRes_ext
  · simp [ExecutableStorage.Block.resource, ExecutableStorage.Block.header,
      ExecutableStorage.heap, present]
  · intro offset
    by_cases inside : offset < block.cells.length
    · by_cases written : address.offset ≤ offset ∧ offset < address.offset + contents.length
      · simp [ExecutableStorage.Block.resource, live, overwrite,
          List.getElem?_ofFn, inside, written]
      · simp [ExecutableStorage.Block.resource, live, overwrite,
          List.getElem?_ofFn, inside, written, ExecutableStorage.heap, present]
    · have outside : ¬ (address.offset ≤ offset ∧ offset < address.offset + contents.length) := by omega
      simp [ExecutableStorage.Block.resource, live, overwrite,
        List.getElem?_ofFn, inside, outside, ExecutableStorage.heap, present]

def WriteRange (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (after : Heap (Excl (Option Byte))) : Prop :=
  ∃ extent, (before address.allocation).1 = .own ⟨extent, true⟩ ∧
    address.offset + contents.length ≤ extent ∧
    (∀ index < contents.length, ∃ old,
      (before address.allocation).2 (address.offset + index) = whole old) ∧
    after = updateRange before address contents

theorem writeBytes_sound (storage next : Storage.State Byte) (address : Address)
    (contents : List (Option Byte)) (executed : writeBytes storage address contents = some next) :
    WriteRange (heap storage) address contents (heap next) := by
  cases present : storage.lookup address.allocation with
  | none => simp [writeBytes, present] at executed
  | some block =>
      by_cases valid : block.live = true ∧ address.offset + contents.length ≤ block.cells.length
      · simp [writeBytes, present, valid] at executed
        subst next
        refine ⟨block.cells.length, ?_, valid.2, ?_, ?_⟩
        · simp [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
            ExecutableStorage.Block.header, valid.1]
        · intro index inside
          have bound : address.offset + index < block.cells.length := by omega
          refine ⟨block.cells[address.offset + index], ?_⟩
          simp [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
            valid.1, List.getElem?_eq_getElem bound]
        · simpa only [valid.1] using
            writeBytes_heap storage address contents block present valid.1 valid.2
      · simp [writeBytes, present, valid] at executed

theorem writeBytes_complete (storage : Storage.State Byte) (address : Address)
    (contents : List (Option Byte)) (after : Heap (Excl (Option Byte)))
    (writable : WriteRange (heap storage) address contents after) :
    ∃ next, writeBytes storage address contents = some next ∧ heap next = after := by
  obtain ⟨extent, header, bounds, _, final⟩ := writable
  cases present : storage.lookup address.allocation with
  | none => simp [heap, ExecutableStorage.heap, present, Excl.zero_def] at header
  | some block =>
      have fields : block.cells.length = extent ∧ block.live = true := by
        simpa [heap, ExecutableStorage.heap, present, ExecutableStorage.Block.resource,
          ExecutableStorage.Block.header] using header
      have valid : address.offset + contents.length ≤ block.cells.length := by omega
      refine ⟨ExecutableStorage.put storage address.allocation
        { block with cells := overwrite block.cells address contents }, ?_, ?_⟩
      · simp [writeBytes, present, fields.2, valid]
      · rw [final]
        exact writeBytes_heap storage address contents block present fields.2 valid

theorem updateRange_header (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (allocation : BlockId) :
    (updateRange before address contents allocation).1 = (before allocation).1 := by
  by_cases same : allocation = address.allocation
  · subst allocation
    simp [updateRange]
  · simp [updateRange, Function.update_of_ne same]

theorem updateRange_outside (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (observed : Address)
    (outside : observed.allocation ≠ address.allocation ∨
      ¬ (address.offset ≤ observed.offset ∧ observed.offset < address.offset + contents.length)) :
    (updateRange before address contents observed.allocation).2 observed.offset =
      (before observed.allocation).2 observed.offset := by
  by_cases same : observed.allocation = address.allocation
  · rcases outside with different | outside
    · exact False.elim (different same)
    · simp [updateRange, same, outside]
  · simp [updateRange, Function.update_of_ne same]

theorem updateRange_inside (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (index : Nat) (inside : index < contents.length) :
    (updateRange before address contents address.allocation).2 (address.offset + index) =
      whole ((contents[index]?).getD none) := by
  have bounds : address.offset ≤ address.offset + index ∧
      address.offset + index < address.offset + contents.length := by omega
  simp [updateRange, bounds]

theorem updateRange_cell (before : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (allocation : BlockId) (offset : Nat) :
    (updateRange before address contents allocation).2 offset =
      if allocation = address.allocation ∧ address.offset ≤ offset ∧
          offset < address.offset + contents.length then
        whole ((contents[offset - address.offset]?).getD none)
      else (before allocation).2 offset := by
  by_cases same : allocation = address.allocation
  · subst allocation
    simp [updateRange]
  · simp [updateRange, same]

theorem WriteRange.read_back (before after : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (written : WriteRange before address contents after) :
    ReadRange after ⟨address, contents.length⟩ contents := by
  obtain ⟨extent, header, bounds, _, rfl⟩ := written
  refine ⟨extent, ?_, bounds, rfl, ?_⟩
  · simpa only [updateRange_header] using header
  · intro index inside
    rw [updateRange_inside before address contents index inside, read_whole]

theorem writeBytes_read_back (storage next : Storage.State Byte) (address : Address)
    (contents : List (Option Byte)) (written : writeBytes storage address contents = some next) :
    readBytes next ⟨address, contents.length⟩ = some contents :=
  readBytes_complete next _ contents
    (WriteRange.read_back _ _ address contents (writeBytes_sound storage next address contents written))

/-- Disjoint byte ranges commute at the complete ownership heap, including
different ranges of the same allocation. They need not have distinct blocks. -/
theorem updateRange_commute (before : Heap (Excl (Option Byte)))
    (left right : Address) (first second : List (Option Byte))
    (disjoint : Range.Disjoint ⟨left, first.length⟩ ⟨right, second.length⟩) :
    updateRange (updateRange before left first) right second =
      updateRange (updateRange before right second) left first := by
  funext allocation
  apply blockRes_ext
  · simp only [updateRange_header]
  · intro offset
    by_cases leftHere : allocation = left.allocation ∧ left.offset ≤ offset ∧
      offset < left.offset + first.length
    · by_cases rightHere : allocation = right.allocation ∧ right.offset ≤ offset ∧
        offset < right.offset + second.length
      · exact False.elim (disjoint.excludes (leftHere.1.symm.trans rightHere.1) offset
          ⟨leftHere.2, rightHere.2⟩)
      · simp only [updateRange_cell, if_pos leftHere, if_neg rightHere]
    · by_cases rightHere : allocation = right.allocation ∧ right.offset ≤ offset ∧
        offset < right.offset + second.length
      · simp only [updateRange_cell, if_neg leftHere, if_pos rightHere]
      · simp only [updateRange_cell, if_neg leftHere, if_neg rightHere]

theorem updateRange_frame (before frame : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (separate : before ## frame)
    (owned : ∀ index < contents.length, ∃ old,
      (before address.allocation).2 (address.offset + index) = whole old) :
    updateRange (before + frame) address contents = updateRange before address contents + frame := by
  funext allocation
  apply blockRes_ext
  · simp only [updateRange_header, heap_add_header]
  · intro offset
    by_cases changed : allocation = address.allocation ∧ address.offset ≤ offset ∧
      offset < address.offset + contents.length
    · have indexBound : offset - address.offset < contents.length := by omega
      obtain ⟨old, held⟩ := owned (offset - address.offset) indexBound
      have offsetEqual : address.offset + (offset - address.offset) = offset := by omega
      rw [offsetEqual, ← changed.1] at held
      have frameZero : (frame allocation).2 offset = 0 :=
        eq_zero_of_whole_separate (held ▸ (separate allocation).2 offset)
      simp only [updateRange_cell, if_pos changed, heap_add_cell, frameZero, SepAlgebra.add_zero]
    · simp only [updateRange_cell, if_neg changed, heap_add_cell]

theorem updateRange_separate (before frame : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (separate : before ## frame)
    (owned : ∀ index < contents.length, ∃ old,
      (before address.allocation).2 (address.offset + index) = whole old) :
    updateRange before address contents ## frame := by
  intro allocation
  refine ⟨?_, ?_⟩
  · simpa only [updateRange_header] using (separate allocation).1
  · intro offset
    by_cases changed : allocation = address.allocation ∧ address.offset ≤ offset ∧
      offset < address.offset + contents.length
    · have indexBound : offset - address.offset < contents.length := by omega
      obtain ⟨old, held⟩ := owned (offset - address.offset) indexBound
      have offsetEqual : address.offset + (offset - address.offset) = offset := by omega
      rw [offsetEqual, ← changed.1] at held
      have frameZero : (frame allocation).2 offset = 0 :=
        eq_zero_of_whole_separate (held ▸ (separate allocation).2 offset)
      rw [updateRange_cell, if_pos changed, frameZero]
      exact SepAlgebra.separate_zero _
    · simpa only [updateRange_cell, if_neg changed] using (separate allocation).2 offset

theorem ReadRange.frame (before frame : Heap (Excl (Option Byte))) (range : Range)
    (contents : List (Option Byte)) (separate : before ## frame)
    (readable : ReadRange before range contents) : ReadRange (before + frame) range contents := by
  obtain ⟨extent, header, bounds, length, bytes⟩ := readable
  have frameHeader := frame_header_empty separate header
  refine ⟨extent, ?_, bounds, length, ?_⟩
  · rw [heap_add_header, header, frameHeader]
    rfl
  · intro index inside
    exact read_add ((separate range.address.allocation).2 (range.address.offset + index))
      (bytes index inside)

theorem WriteRange.frame (before after frame : Heap (Excl (Option Byte))) (address : Address)
    (contents : List (Option Byte)) (separate : before ## frame)
    (written : WriteRange before address contents after) :
    WriteRange (before + frame) address contents (after + frame) ∧ after ## frame := by
  obtain ⟨extent, header, bounds, owned, rfl⟩ := written
  have frameHeader := frame_header_empty separate header
  refine ⟨⟨extent, ?_, bounds, ?_, ?_⟩,
    updateRange_separate before frame address contents separate owned⟩
  · rw [heap_add_header, header, frameHeader]
    rfl
  · intro index inside
    obtain ⟨old, held⟩ := owned index inside
    have frameZero : (frame address.allocation).2 (address.offset + index) = 0 :=
      eq_zero_of_whole_separate (held ▸ (separate address.allocation).2 (address.offset + index))
    exact ⟨old, by rw [heap_add_cell, held, frameZero, SepAlgebra.add_zero]⟩
  · exact (updateRange_frame before frame address contents separate owned).symm

/-- Copy observes the source once, then writes that snapshot. Overlap is
allowed here; a library memcpy contract must additionally exclude overlap
and carry effective-type information. -/
def copyBytes (storage : Storage.State Byte) (source : Range) (target : Address) :
    Option (Storage.State Byte) := do
  let contents ← readBytes storage source
  writeBytes storage target contents

def CopyRange (before : Heap (Excl (Option Byte))) (source : Range) (target : Address)
    (after : Heap (Excl (Option Byte))) : Prop :=
  ∃ contents, ReadRange before source contents ∧ WriteRange before target contents after

theorem copyBytes_sound (storage next : Storage.State Byte) (source : Range) (target : Address)
    (executed : copyBytes storage source target = some next) :
    CopyRange (heap storage) source target (heap next) := by
  cases observed : readBytes storage source with
  | none => simp [copyBytes, observed] at executed
  | some contents =>
      have written : writeBytes storage target contents = some next := by
        simpa [copyBytes, observed] using executed
      exact ⟨contents, readBytes_sound storage source contents observed,
        writeBytes_sound storage next target contents written⟩

theorem copyBytes_complete (storage : Storage.State Byte) (source : Range) (target : Address)
    (after : Heap (Excl (Option Byte))) (copied : CopyRange (heap storage) source target after) :
    ∃ next, copyBytes storage source target = some next ∧ heap next = after := by
  obtain ⟨contents, readable, writable⟩ := copied
  have observed := readBytes_complete storage source contents readable
  obtain ⟨next, written, final⟩ := writeBytes_complete storage target contents after writable
  exact ⟨next, by simp [copyBytes, observed, written], final⟩

end Mettapedia.Languages.C11.ByteRanges
