import Mettapedia.Languages.C11.IntegerObject

/-!
# Integer representations connected to the byte memory kernel

The executable reader first observes a complete raw byte range and then
interprets its initialized representation. The independent rule joins the
owned byte-range read to the integer object's reading judgment. A typed
writer accepts a proved valid integer value and writes a constructed ordinary
representation. Every admitted write followed by its corresponding read
returns that value, for arbitrary live allocations and admitted object
profiles. Read and write judgments preserve disjoint resource frames.

These are representation-memory operations. Their source lvalue adapters
must additionally establish alignment, effective type and access policy.
Indeterminate bytes have no constructed initialized-value result here; this
does not classify every indeterminate C11 expression as undefined behavior.
Character reads and padding/unspecified-value choices require their own
source rules. Trap classification is retained separately from memory refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerMemory

open ByteStorageData ByteRanges
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

def initialized {Byte : Type} : List (Option Byte) → Option (List Byte)
  | [] => some []
  | none :: _ => none
  | some head :: tail => do
      let rest ← initialized tail
      some (head :: rest)

theorem initialized_some {Byte : Type} (bytes : List Byte) : initialized (bytes.map some) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
      change (initialized (tail.map some)).bind (fun rest => some (head :: rest)) = some (head :: tail)
      rw [ih]
      rfl

theorem initialized_exact {Byte : Type} (raw : List (Option Byte)) (bytes : List Byte)
    (accepted : initialized raw = some bytes) : raw = bytes.map some := by
  induction raw generalizing bytes with
  | nil => simp [initialized] at accepted; subst bytes; rfl
  | cons head tail ih =>
      cases head with
      | none => simp [initialized] at accepted
      | some head =>
          cases decoded : initialized tail with
          | none => simp [initialized, decoded] at accepted
          | some rest =>
              simp [initialized, decoded] at accepted
              subst bytes
              simp only [List.map_cons, ih rest decoded]

theorem initialized_iff {Byte : Type} (raw : List (Option Byte)) (bytes : List Byte) :
    initialized raw = some bytes ↔ raw = bytes.map some := by
  constructor
  · exact initialized_exact raw bytes
  · rintro rfl
    exact initialized_some bytes

def readInteger (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (address : Address) : Option IntegerObject.Outcome := do
  let raw ← readBytes storage ⟨address, profile.byteCount⟩
  let bytes ← initialized raw
  IntegerObject.readObject profile bytes

def Reading (profile : IntegerObject.Profile) (memory : Heap (Excl (Option (Byte profile.characters))))
    (address : Address) (outcome : IntegerObject.Outcome) : Prop :=
  ∃ bytes : List (Byte profile.characters),
    ReadRange memory ⟨address, profile.byteCount⟩ (bytes.map some) ∧ IntegerObject.Reading profile bytes outcome

theorem readInteger_sound (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (address : Address) (outcome : IntegerObject.Outcome) (computed : readInteger profile storage address = some outcome) :
    Reading profile (ByteRanges.heap storage) address outcome := by
  cases observed : readBytes storage ⟨address, profile.byteCount⟩ with
  | none => simp [readInteger, observed] at computed
  | some raw =>
      cases known : initialized raw with
      | none => simp [readInteger, observed, known] at computed
      | some bytes =>
          have shape := initialized_exact raw bytes known
          have read := readBytes_sound storage ⟨address, profile.byteCount⟩ raw observed
          rw [shape] at read
          refine ⟨bytes, read, IntegerObject.readObject_sound profile bytes outcome ?_⟩
          simpa [readInteger, observed, known] using computed

theorem readInteger_complete (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (address : Address) (outcome : IntegerObject.Outcome)
    (reading : Reading profile (ByteRanges.heap storage) address outcome) : readInteger profile storage address = some outcome := by
  obtain ⟨bytes, read, integer⟩ := reading
  have observed := readBytes_complete storage ⟨address, profile.byteCount⟩ (bytes.map some) read
  have interpreted := IntegerObject.readObject_complete profile bytes outcome integer
  simp [readInteger, observed, initialized_some, interpreted]

theorem readInteger_iff (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (address : Address) (outcome : IntegerObject.Outcome) :
    readInteger profile storage address = some outcome ↔ Reading profile (ByteRanges.heap storage) address outcome :=
  ⟨readInteger_sound profile storage address outcome, readInteger_complete profile storage address outcome⟩

def storeInteger (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (address : Address) (value : IntegerValue profile.integer) : Option (Storage.State (Byte profile.characters)) :=
  writeBytes storage address ((IntegerObject.storeObject profile value.value).map some)

def Writing (profile : IntegerObject.Profile) (before after : Heap (Excl (Option (Byte profile.characters))))
    (address : Address) (value : IntegerValue profile.integer) : Prop :=
  WriteRange before address ((IntegerObject.storeObject profile value.value).map some) after

theorem storeInteger_sound (profile : IntegerObject.Profile) (storage saved : Storage.State (Byte profile.characters))
    (address : Address) (value : IntegerValue profile.integer)
    (computed : storeInteger profile storage address value = some saved) :
    Writing profile (ByteRanges.heap storage) (ByteRanges.heap saved) address value :=
  writeBytes_sound storage saved address _ computed

theorem storeInteger_complete (profile : IntegerObject.Profile) (storage : Storage.State (Byte profile.characters))
    (after : Heap (Excl (Option (Byte profile.characters)))) (address : Address) (value : IntegerValue profile.integer)
    (writing : Writing profile (ByteRanges.heap storage) after address value) :
    ∃ saved, storeInteger profile storage address value = some saved ∧ ByteRanges.heap saved = after :=
  writeBytes_complete storage address _ after writing

theorem read_after_store (profile : IntegerObject.Profile) (storage saved : Storage.State (Byte profile.characters))
    (address : Address) (value : IntegerValue profile.integer)
    (computed : storeInteger profile storage address value = some saved) :
    readInteger profile saved address = some (.integer (.value value.value false)) := by
  have observed := writeBytes_read_back storage saved address _ computed
  rw [List.length_map, IntegerObject.storeObject_extent] at observed
  simp [readInteger, observed, initialized_some, IntegerObject.readObject_storeObject profile value.value value.valid]

theorem Reading.frame (profile : IntegerObject.Profile) (before frame : Heap (Excl (Option (Byte profile.characters))))
    (address : Address) (outcome : IntegerObject.Outcome) (reading : Reading profile before address outcome)
    (separate : before ## frame) : Reading profile (before + frame) address outcome := by
  obtain ⟨bytes, read, interpreted⟩ := reading
  exact ⟨bytes, ByteRanges.ReadRange.frame before frame ⟨address, profile.byteCount⟩ _ separate read, interpreted⟩

theorem Writing.frame (profile : IntegerObject.Profile)
    (before after frame : Heap (Excl (Option (Byte profile.characters))))
    (address : Address) (value : IntegerValue profile.integer) (writing : Writing profile before after address value)
    (separate : before ## frame) : Writing profile (before + frame) (after + frame) address value ∧ after ## frame :=
  ByteRanges.WriteRange.frame before after frame address _ separate writing

end Mettapedia.Languages.C11.IntegerMemory
