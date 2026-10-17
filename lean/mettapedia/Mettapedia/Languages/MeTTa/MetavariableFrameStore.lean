import Mathlib.Data.List.FinRange
import Mettapedia.Languages.MeTTa.MetavariableFrame

/-!
# Generational indexed stores for metavariable frames

The directory and each frame's values are arrays. A reference carries a
directory handle, allocation generation, and slot; lookup does not inspect
variable names. An outer `none` means an invalid reference, whereas `some none`
means a valid, unbound slot.

The first model uses unbounded natural generations within one store lineage.
Rollback restores a saved directory but retains the current allocation
counter; its invariant requires a snapshot from an earlier counter. The
`Shared` model instead gives branch images one finite-generation allocator,
checked owner-count transitions, and permanent retirement at exhaustion.
Independent allocators do not share an identity namespace. Payloads are arbitrary
universe-polymorphic values; the original `Atom` API specializes the same carrier.
Payload retention does not interpret or materialize a contextual value. Relating either protocol to
runtime pointer ownership, C code, or physical complexity remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrame (Frame Slot FrameEnv FrameEnvOf)

universe u v w

variable {Payload : Type u}

/-- Coordinates are interpreted only in their owning store lineage. -/
structure Ref where
  handle : Nat
  generation : Nat
  slot : Nat
  deriving DecidableEq, Repr

/-- The authored inventory remains available for the named semantic boundary. -/
structure EntryOf (Payload : Type u) where
  generation : Nat
  frame : Frame
  values : Array (Option Payload)
  size_eq : values.size = frame.length
  writeVersions : Array Nat
  versions_size_eq : writeVersions.size = frame.length
  activationBoundary : Option Nat

/-- Initial contents precede the activation; only subsequent writes consume
directory-clock readings. This constructor does not model a native write. -/
def EntryOf.initial (generation : Nat) (frame : Frame)
    (env : FrameEnvOf Payload frame) : EntryOf Payload :=
  ⟨generation, frame, Array.ofFn env, by simp,
    Array.replicate frame.length 0, by simp, none⟩

/-- Syntax-valued entries retain the original API. -/
abbrev Entry := EntryOf Atom

structure StoreOf (Payload : Type u) where
  entries : Array (Option (EntryOf Payload))
  nextGeneration : Nat
  writeClock : Nat

/-- Syntax-valued stores retain the original API. -/
abbrev Store := StoreOf Atom

def StoreOf.empty (capacity : Nat) : StoreOf Payload :=
  ⟨Array.replicate capacity none, 0, 0⟩

/-- The original constructor chooses syntax payloads when no type is supplied. -/
abbrev empty (capacity : Nat) : Store := StoreOf.empty capacity

def frameAt (store : StoreOf Payload) (handle : Nat) : Option (EntryOf Payload) :=
  (store.entries[handle]?).getD none

def lookup (store : StoreOf Payload) (ref : Ref) : Option (Option Payload) := do
  let entry ← frameAt store ref.handle
  if entry.generation = ref.generation then entry.values[ref.slot]? else none

/-- Every installed generation has already been consumed by the allocator. -/
def WellFormed (store : StoreOf Payload) : Prop :=
  ∀ handle entry, frameAt store handle = some entry →
    entry.generation < store.nextGeneration

private def replace (store : StoreOf Payload) (handle : Nat) (entry : EntryOf Payload) : StoreOf Payload :=
  { store with
    entries := store.entries.setIfInBounds handle (some entry)
    writeClock := store.writeClock + 1 }

private theorem frameAt_replace_self (store : StoreOf Payload) (handle : Nat)
    (bound : handle < store.entries.size) (entry : EntryOf Payload) :
    frameAt (replace store handle entry) handle = some entry := by
  simp [frameAt, replace, Array.getElem?_setIfInBounds_self_of_lt bound]

private theorem frameAt_replace_other (store : StoreOf Payload) (handle other : Nat)
    (distinct : handle ≠ other) (entry : EntryOf Payload) :
    frameAt (replace store handle entry) other = frameAt store other := by
  simp [frameAt, replace, Array.getElem?_setIfInBounds_ne distinct]

private theorem frameAt_bound {store : StoreOf Payload} {handle : Nat} {entry : EntryOf Payload}
    (present : frameAt store handle = some entry) : handle < store.entries.size := by
  by_contra outside
  simp [frameAt, Array.getElem?_eq_none (Nat.not_lt.mp outside)] at present

/-- Replace any prior activation at this handle by a fresh allocation. -/
def install (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) : StoreOf Payload :=
  { entries := store.entries.setIfInBounds handle.val
      (some (EntryOf.initial store.nextGeneration frame env))
    nextGeneration := store.nextGeneration + 1
    writeClock := store.writeClock }

def allocatedRef (store : StoreOf Payload) (handle : Fin store.entries.size)
    {frame : Frame} (slot : Slot frame) : Ref :=
  ⟨handle.val, store.nextGeneration, slot.val⟩

/-- Convert the concrete array back to the existing semantic frame carrier. -/
def entryEnv (entry : EntryOf Payload) : FrameEnvOf Payload entry.frame :=
  fun slot => entry.values[slot.val]'(by rw [entry.size_eq]; exact slot.isLt)

/-- A guarded raw slot read keeps valid unbound slots and their versions.
The clock is the directory's reading, while the boundary belongs to the frame.
This is an operational data view, not a decoder of C pointers or layout. -/
structure SlotReadbackOf (Payload : Type u) where
  value : Option Payload
  writeVersion : Nat
  writeClock : Nat
  activationBoundary : Option Nat
  deriving DecidableEq, Repr

def SlotReadbackOf.mapPayload {Target : Type v} (f : Payload → Target)
    (row : SlotReadbackOf Payload) : SlotReadbackOf Target :=
  ⟨row.value.map f, row.writeVersion, row.writeClock, row.activationBoundary⟩

/-- With no activation boundary, all stored values are observable. An active
boundary admits precisely bound slots whose write follows it. -/
def SlotReadbackOf.activationOutput (row : SlotReadbackOf Payload) : Option Payload :=
  if row.activationBoundary.all (fun boundary => decide (boundary < row.writeVersion))
    then row.value else none

/-- A retained activation view keeps its own boundary across later projections. -/
def SlotReadbackOf.outputAfter (boundary : Nat) (row : SlotReadbackOf Payload) : Option Payload :=
  if boundary < row.writeVersion then row.value else none

def EntryOf.readSlot? (entry : EntryOf Payload) (clock slot : Nat) : Option (SlotReadbackOf Payload) :=
  match entry.values[slot]?, entry.writeVersions[slot]? with
  | some value, some version => some ⟨value, version, clock, entry.activationBoundary⟩
  | _, _ => none

/-- The same generation and bounds guards protect values and lineage metadata. -/
def readSlot? (store : StoreOf Payload) (ref : Ref) : Option (SlotReadbackOf Payload) := do
  let entry ← frameAt store ref.handle
  if entry.generation = ref.generation then entry.readSlot? store.writeClock ref.slot else none

theorem readSlot?_of_frameAt {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (generation : entry.generation = ref.generation) :
    readSlot? store ref = entry.readSlot? store.writeClock ref.slot := by
  simp [readSlot?, present, generation]

theorem readSlot?_stale {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (stale : entry.generation ≠ ref.generation) : readSlot? store ref = none := by
  simp [readSlot?, present, stale]

theorem EntryOf.readSlot?_valid (entry : EntryOf Payload) (clock : Nat) (slot : Slot entry.frame) :
    entry.readSlot? clock slot.val =
      some ⟨entryEnv entry slot,
        entry.writeVersions[slot.val]'(by rw [entry.versions_size_eq]; exact slot.isLt),
        clock, entry.activationBoundary⟩ := by
  simp [EntryOf.readSlot?, entryEnv, entry.size_eq, entry.versions_size_eq, slot.isLt]

/-- Project assignments within the same inventory. Selected unbound slots keep
their versions; the frame boundary is independent of every slot's boundness. -/
def EntryOf.projectSlots (entry : EntryOf Payload) (keep : Nat → Bool) : EntryOf Payload :=
  { entry with
    values := Array.ofFn (fun slot : Slot entry.frame =>
      if keep slot.val then entryEnv entry slot else none)
    size_eq := by simp
    writeVersions := Array.ofFn (fun slot : Slot entry.frame =>
      if keep slot.val then
        entry.writeVersions[slot.val]'(by rw [entry.versions_size_eq]; exact slot.isLt)
      else 0)
    versions_size_eq := by simp }

theorem EntryOf.readSlot?_projectSlots (entry : EntryOf Payload) (keep : Nat → Bool)
    (clock : Nat) (slot : Slot entry.frame) :
    (entry.projectSlots keep).readSlot? clock slot.val =
      (entry.readSlot? clock slot.val).map (fun row =>
        { row with
          value := if keep slot.val then row.value else none
          writeVersion := if keep slot.val then row.writeVersion else 0 }) := by
  simp [EntryOf.readSlot?, EntryOf.projectSlots, entryEnv,
    entry.size_eq, entry.versions_size_eq, slot.isLt]

theorem lookup_of_frameAt {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (generation : entry.generation = ref.generation) :
    lookup store ref = entry.values[ref.slot]? := by
  simp [lookup, present, generation]

theorem lookup_stale {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (stale : entry.generation ≠ ref.generation) : lookup store ref = none := by
  simp [lookup, present, stale]

theorem lookup_slot {store : StoreOf Payload} {handle : Nat} {entry : EntryOf Payload}
    (present : frameAt store handle = some entry) (slot : Slot entry.frame) :
    lookup store ⟨handle, entry.generation, slot.val⟩ = some (entryEnv entry slot) := by
  rw [lookup_of_frameAt present rfl]
  simp [entryEnv]

theorem lookup_named {store : StoreOf Payload} {handle : Nat} {entry : EntryOf Payload}
    (present : frameAt store handle = some entry) (unique : entry.frame.Nodup)
    (slot : Slot entry.frame) :
    lookup store ⟨handle, entry.generation, slot.val⟩ =
      some (MetavariableFrame.denote (entryEnv entry) (MetavariableFrame.nameOf slot)) := by
  rw [MetavariableFrame.denote_nameOf unique]
  exact lookup_slot present slot

theorem frameAt_install_self (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) :
    frameAt (install store handle frame env) handle.val =
      some (EntryOf.initial store.nextGeneration frame env) := by
  simp [frameAt, install]

theorem lookup_install (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) (slot : Slot frame) :
    lookup (install store handle frame env) (allocatedRef store handle slot) =
      some (env slot) := by
  simp [lookup, allocatedRef, frameAt_install_self, EntryOf.initial, slot.isLt]

theorem lookup_install_other (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) (ref : Ref)
    (distinct : handle.val ≠ ref.handle) :
    lookup (install store handle frame env) ref = lookup store ref := by
  simp [lookup, frameAt, install, Array.getElem?_setIfInBounds_ne distinct]

/-- Reusing a handle rejects every older generation, for every slot. -/
theorem lookup_install_stale (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) (generation slot : Nat)
    (older : generation < store.nextGeneration) :
    lookup (install store handle frame env) ⟨handle.val, generation, slot⟩ = none := by
  apply lookup_stale (frameAt_install_self store handle frame env)
  exact Nat.ne_of_gt older

theorem reuse_rejects_old {store : StoreOf Payload} (wellFormed : WellFormed store)
    (handle : Fin store.entries.size) {old : EntryOf Payload}
    (present : frameAt store handle.val = some old)
    (frame : Frame) (env : FrameEnvOf Payload frame) (slot : Nat) :
    lookup (install store handle frame env) ⟨handle.val, old.generation, slot⟩ = none :=
  lookup_install_stale store handle frame env old.generation slot
    (wellFormed handle.val old present)

private def updateEntry (entry : EntryOf Payload) (slot : Nat) (value : Option Payload)
    (version : Nat) : EntryOf Payload :=
  { entry with
    values := entry.values.setIfInBounds slot value
    size_eq := by simpa using entry.size_eq
    writeVersions := entry.writeVersions.setIfInBounds slot version
    versions_size_eq := by simpa using entry.versions_size_eq }

/-- Writes reject missing frames, stale generations, and invalid slots. -/
def write? (store : StoreOf Payload) (ref : Ref) (value : Option Payload) : Option (StoreOf Payload) := do
  let entry ← frameAt store ref.handle
  if entry.generation = ref.generation ∧ ref.slot < entry.values.size then
    some (replace store ref.handle (updateEntry entry ref.slot value (store.writeClock + 1)))
  else none

theorem write?_valid {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (generation : entry.generation = ref.generation)
    (bound : ref.slot < entry.values.size) (value : Option Payload) :
    write? store ref value =
      some (replace store ref.handle (updateEntry entry ref.slot value (store.writeClock + 1))) := by
  simp [write?, present, generation, bound]

theorem write?_stale {store : StoreOf Payload} {ref : Ref} {entry : EntryOf Payload}
    (present : frameAt store ref.handle = some entry)
    (stale : entry.generation ≠ ref.generation) (value : Option Payload) :
    write? store ref value = none := by
  simp [write?, present, stale]

private theorem write?_success {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) :
    ∃ entry, frameAt store ref.handle = some entry ∧
      entry.generation = ref.generation ∧ ref.slot < entry.values.size ∧
      next = replace store ref.handle (updateEntry entry ref.slot value (store.writeClock + 1)) := by
  cases present : frameAt store ref.handle with
  | none => simp [write?, present] at written
  | some entry =>
    simp only [write?, present] at written
    change (if entry.generation = ref.generation ∧ ref.slot < entry.values.size then
      some (replace store ref.handle (updateEntry entry ref.slot value (store.writeClock + 1))) else none) =
      some next at written
    split at written
    · next valid =>
      exact ⟨entry, rfl, valid.1, valid.2, (Option.some.inj written).symm⟩
    · simp at written

theorem lookup_write {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) : lookup next ref = some value := by
  obtain ⟨entry, present, generation, bound, rfl⟩ := write?_success written
  rw [lookup_of_frameAt (entry := updateEntry entry ref.slot value (store.writeClock + 1))
    (frameAt_replace_self store ref.handle (frameAt_bound present) _) generation]
  simp [updateEntry, Array.getElem?_setIfInBounds_self_of_lt bound]

/-- Every reference with different coordinates retains its old observation. -/
theorem lookup_write_other {store next : StoreOf Payload} {ref other : Ref} {value : Option Payload}
    (written : write? store ref value = some next) (distinct : other ≠ ref) :
    lookup next other = lookup store other := by
  obtain ⟨entry, present, generation, bound, rfl⟩ := write?_success written
  by_cases sameHandle : ref.handle = other.handle
  · have otherPresent : frameAt store other.handle = some entry := sameHandle ▸ present
    have changedPresent :
        frameAt (replace store ref.handle (updateEntry entry ref.slot value (store.writeClock + 1))) other.handle =
          some (updateEntry entry ref.slot value (store.writeClock + 1)) := by
      rw [← sameHandle]
      exact frameAt_replace_self store ref.handle (frameAt_bound present) _
    by_cases sameGeneration : entry.generation = other.generation
    · have differentSlot : ref.slot ≠ other.slot := by
        intro sameSlot
        apply distinct
        cases ref
        cases other
        simp_all
      rw [lookup_of_frameAt changedPresent sameGeneration,
        lookup_of_frameAt otherPresent sameGeneration]
      simp [updateEntry, Array.getElem?_setIfInBounds_ne differentSlot]
    · rw [lookup_stale changedPresent sameGeneration, lookup_stale otherPresent sameGeneration]
  · simp [lookup, frameAt_replace_other store ref.handle other.handle sameHandle]

theorem write_preserves_counter {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) :
    next.nextGeneration = store.nextGeneration := by
  obtain ⟨_, _, _, _, rfl⟩ := write?_success written
  rfl

theorem write_advances_clock {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) : next.writeClock = store.writeClock + 1 := by
  obtain ⟨_, _, _, _, rfl⟩ := write?_success written
  rfl

/-- A successful write stamps the slot even when its new value is unbound.
No activation boundary or allocation identity is reset. -/
theorem readSlot?_write {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) :
    ∃ boundary, readSlot? next ref = some ⟨value, next.writeClock, next.writeClock, boundary⟩ ∧
      (frameAt store ref.handle).map EntryOf.activationBoundary = some boundary := by
  obtain ⟨entry, present, generation, bound, rfl⟩ := write?_success written
  have versionBound : ref.slot < entry.writeVersions.size := by
    rw [entry.versions_size_eq, ← entry.size_eq]
    exact bound
  refine ⟨entry.activationBoundary, ?_, by simp [present]⟩
  rw [readSlot?_of_frameAt (entry := updateEntry entry ref.slot value (store.writeClock + 1))
    (frameAt_replace_self store ref.handle (frameAt_bound present) _) generation]
  simp [EntryOf.readSlot?, updateEntry, replace,
    Array.getElem?_setIfInBounds_self_of_lt bound,
    Array.getElem?_setIfInBounds_self_of_lt versionBound]

/-- Marking activation is a frame operation; it consumes no slot-write reading. -/
def activate? (store : StoreOf Payload) (handle generation : Nat) : Option (StoreOf Payload) := do
  let entry ← frameAt store handle
  if entry.generation = generation then
    some { store with
      entries := store.entries.setIfInBounds handle
        (some { entry with activationBoundary := some store.writeClock }) }
  else none

theorem activate?_valid {store : StoreOf Payload} {handle generation : Nat} {entry : EntryOf Payload}
    (present : frameAt store handle = some entry) (same : entry.generation = generation) :
    activate? store handle generation = some { store with
      entries := store.entries.setIfInBounds handle
        (some { entry with activationBoundary := some store.writeClock }) } := by
  simp [activate?, present, same]

theorem activate_preserves_clock {store next : StoreOf Payload} {handle generation : Nat}
    (activated : activate? store handle generation = some next) : next.writeClock = store.writeClock := by
  cases present : frameAt store handle with
  | none => simp [activate?, present] at activated
  | some entry =>
    simp only [activate?, present, Option.bind_eq_bind, Option.bind_some] at activated
    split at activated
    · cases Option.some.inj activated; rfl
    · simp at activated

/-- Snapshot rollback restores all values and identities but not allocation history. -/
def rollback (current saved : StoreOf Payload) : StoreOf Payload :=
  { entries := saved.entries, nextGeneration := current.nextGeneration
    writeClock := current.writeClock }

theorem lookup_rollback (current saved : StoreOf Payload) (ref : Ref) :
    lookup (rollback current saved) ref = lookup saved ref := by
  simp [lookup, frameAt, rollback]

theorem rollback_preserves_counter (current saved : StoreOf Payload) :
    (rollback current saved).nextGeneration = current.nextGeneration := rfl

/-- Rollback restores the saved slot histories while keeping the current clock. -/
theorem readSlot?_rollback (current saved : StoreOf Payload) (ref : Ref) :
    readSlot? (rollback current saved) ref =
      (readSlot? saved ref).map (fun row => { row with writeClock := current.writeClock }) := by
  unfold readSlot?
  simp only [frameAt, rollback]
  cases (saved.entries[ref.handle]?).getD none with
  | none => rfl
  | some entry =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · simp only [EntryOf.readSlot?]
      cases entry.values[ref.slot]? <;> cases entry.writeVersions[ref.slot]? <;> rfl
    · rfl

theorem rollback_preserves_clock (current saved : StoreOf Payload) :
    (rollback current saved).writeClock = current.writeClock := rfl

theorem empty_wellFormed (capacity : Nat) : WellFormed (StoreOf.empty (Payload := Payload) capacity) := by
  intro handle entry present
  simp [frameAt, StoreOf.empty, Array.getElem?_replicate] at present
  split at present <;> simp_all

theorem install_wellFormed {store : StoreOf Payload} (wellFormed : WellFormed store)
    (handle : Fin store.entries.size) (frame : Frame) (env : FrameEnvOf Payload frame) :
    WellFormed (install store handle frame env) := by
  intro other entry present
  by_cases same : handle.val = other
  · subst other
    rw [frameAt_install_self] at present
    cases Option.some.inj present
    exact Nat.lt_succ_self _
  · have oldPresent : frameAt store other = some entry := by
      simpa [frameAt, install, Array.getElem?_setIfInBounds_ne same] using present
    exact Nat.lt_trans (wellFormed other entry oldPresent) (Nat.lt_succ_self _)

theorem write_wellFormed {store next : StoreOf Payload} (wellFormed : WellFormed store)
    {ref : Ref} {value : Option Payload} (written : write? store ref value = some next) :
    WellFormed next := by
  obtain ⟨entry, present, _, _, rfl⟩ := write?_success written
  intro handle found foundPresent
  by_cases same : ref.handle = handle
  · subst handle
    rw [frameAt_replace_self store ref.handle (frameAt_bound present)] at foundPresent
    cases Option.some.inj foundPresent
    exact wellFormed ref.handle entry present
  · rw [frameAt_replace_other store ref.handle handle same] at foundPresent
    exact wellFormed handle found foundPresent

theorem rollback_wellFormed {current saved : StoreOf Payload} (savedValid : WellFormed saved)
    (earlier : saved.nextGeneration ≤ current.nextGeneration) :
    WellFormed (rollback current saved) := by
  intro handle entry present
  exact Nat.lt_of_lt_of_le (savedValid handle entry present) earlier

/-- Undoing a write restores each observation, including the overwritten slot. -/
theorem rollback_write {store next : StoreOf Payload} {ref : Ref} {value : Option Payload}
    (written : write? store ref value = some next) (observed : Ref) :
    lookup (rollback next store) observed = lookup store observed ∧
      (rollback next store).nextGeneration = store.nextGeneration := by
  exact ⟨lookup_rollback next store observed, by
    rw [rollback_preserves_counter, write_preserves_counter written]⟩

/-- An allocation discarded by rollback is not revived by the next reuse. -/
theorem rollback_reallocate_rejects_discarded (saved : StoreOf Payload)
    (handle : Fin saved.entries.size) (oldFrame newFrame : Frame)
    (oldEnv : FrameEnvOf Payload oldFrame) (newEnv : FrameEnvOf Payload newFrame) (slot : Slot oldFrame) :
    let speculative := install saved handle oldFrame oldEnv
    let restored := rollback speculative saved
    lookup (install restored handle newFrame newEnv) (allocatedRef saved handle slot) =
      none := by
  apply lookup_install_stale
  exact Nat.lt_succ_self _

/-- Allocation after rollback consumes the current counter, regardless of the saved one. -/
theorem rollback_reallocate_generation (current saved : StoreOf Payload)
    (handle : Fin saved.entries.size) {frame : Frame} (slot : Slot frame) :
    (allocatedRef (rollback current saved) handle slot).generation =
      current.nextGeneration := rfl

/-! ## Payload transport

Transport maps values only. Frame inventories, handles, generations, validity
checks, and allocation history are unchanged, even for noninjective maps.
-/

def EntryOf.mapPayload {Target : Type v} (f : Payload → Target)
    (entry : EntryOf Payload) : EntryOf Target :=
  { generation := entry.generation
    frame := entry.frame
    values := entry.values.map (Option.map f)
    size_eq := by simpa using entry.size_eq
    writeVersions := entry.writeVersions
    versions_size_eq := entry.versions_size_eq
    activationBoundary := entry.activationBoundary }

@[simp] theorem entryEnv_mapPayload {Target : Type v} (f : Payload → Target)
    (entry : EntryOf Payload) :
    entryEnv (entry.mapPayload f) = MetavariableFrame.mapPayload f (entryEnv entry) := by
  funext slot
  simp [entryEnv, EntryOf.mapPayload, MetavariableFrame.mapPayload]

def StoreOf.mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) : StoreOf Target :=
  { entries := store.entries.map (Option.map (EntryOf.mapPayload f))
    nextGeneration := store.nextGeneration
    writeClock := store.writeClock }

@[simp] theorem EntryOf.readSlot?_mapPayload {Target : Type v} (f : Payload → Target)
    (entry : EntryOf Payload) (clock slot : Nat) :
    (entry.mapPayload f).readSlot? clock slot =
      (entry.readSlot? clock slot).map (SlotReadbackOf.mapPayload f) := by
  simp only [EntryOf.readSlot?, EntryOf.mapPayload, Array.getElem?_map]
  cases entry.values[slot]? <;> cases entry.writeVersions[slot]? <;> rfl

@[simp] theorem frameAt_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (handle : Nat) :
    frameAt (store.mapPayload f) handle = (frameAt store handle).map (EntryOf.mapPayload f) := by
  simp only [frameAt, StoreOf.mapPayload, Array.getElem?_map]
  cases store.entries[handle]? <;> rfl

@[simp] theorem lookup_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (ref : Ref) :
    lookup (store.mapPayload f) ref = (lookup store ref).map (Option.map f) := by
  unfold lookup
  rw [frameAt_mapPayload]
  cases frameAt store ref.handle with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, EntryOf.mapPayload]
    split <;> simp [Array.getElem?_map]

@[simp] theorem readSlot?_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (ref : Ref) :
    readSlot? (store.mapPayload f) ref = (readSlot? store ref).map (SlotReadbackOf.mapPayload f) := by
  unfold readSlot?
  rw [frameAt_mapPayload]
  cases frameAt store ref.handle with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    change (if entry.generation = ref.generation then
      (entry.mapPayload f).readSlot? store.writeClock ref.slot else none) = _
    split <;> simp [EntryOf.readSlot?_mapPayload]

theorem activate?_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (handle generation : Nat) :
    activate? (store.mapPayload f) handle generation =
      (activate? store handle generation).map (StoreOf.mapPayload f) := by
  unfold activate?
  rw [frameAt_mapPayload]
  cases frameAt store handle with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    change (if entry.generation = generation then
      some { store.mapPayload f with
        entries := (store.mapPayload f).entries.setIfInBounds handle
          (some { entry.mapPayload f with activationBoundary := some store.writeClock }) }
      else none) = _
    split <;> simp [StoreOf.mapPayload, EntryOf.mapPayload]

private theorem mapPayload_replace {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (handle : Nat) (entry : EntryOf Payload) :
    (replace store handle entry).mapPayload f =
      replace (store.mapPayload f) handle (entry.mapPayload f) := by
  simp [StoreOf.mapPayload, replace]

private theorem mapPayload_updateEntry {Target : Type v} (f : Payload → Target)
    (entry : EntryOf Payload) (slot : Nat) (value : Option Payload) (version : Nat) :
    (updateEntry entry slot value version).mapPayload f =
      updateEntry (entry.mapPayload f) slot (value.map f) version := by
  simp [EntryOf.mapPayload, updateEntry]

/-- Successful writes and every failed guard commute with payload transport. -/
theorem write?_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (ref : Ref) (value : Option Payload) :
    write? (store.mapPayload f) ref (value.map f) =
      (write? store ref value).map (StoreOf.mapPayload f) := by
  unfold write?
  rw [frameAt_mapPayload]
  cases frameAt store ref.handle with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some,
      EntryOf.mapPayload, Array.size_map]
    change (if entry.generation = ref.generation ∧ ref.slot < entry.values.size then
      some (replace (store.mapPayload f) ref.handle
        (updateEntry (entry.mapPayload f) ref.slot (value.map f) (store.writeClock + 1))) else none) = _
    split <;> simp [mapPayload_replace, mapPayload_updateEntry]

@[simp] theorem rollback_mapPayload {Target : Type v} (f : Payload → Target)
    (current saved : StoreOf Payload) :
    (rollback current saved).mapPayload f =
      rollback (current.mapPayload f) (saved.mapPayload f) := rfl

theorem install_mapPayload {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnvOf Payload frame) :
    (install store handle frame env).mapPayload f =
      install (store.mapPayload f) ⟨handle.val, by simp [StoreOf.mapPayload]⟩
        frame (MetavariableFrame.mapPayload f env) := by
  simp [StoreOf.mapPayload, EntryOf.mapPayload, EntryOf.initial, install,
    Array.map_ofFn]
  rfl

theorem EntryOf.mapPayload_id (entry : EntryOf Payload) :
    entry.mapPayload id = entry := by
  cases entry
  simp [EntryOf.mapPayload]

theorem EntryOf.mapPayload_comp {Middle : Type v} {Target : Type w}
    (f : Payload → Middle) (g : Middle → Target) (entry : EntryOf Payload) :
    (entry.mapPayload f).mapPayload g = entry.mapPayload (g ∘ f) := by
  simp [EntryOf.mapPayload, Array.map_map, Option.map_map, Function.comp_def]

theorem StoreOf.mapPayload_id (store : StoreOf Payload) :
    store.mapPayload id = store := by
  have identity : Option.map (EntryOf.mapPayload (Payload := Payload) id) = id := by
    funext value
    cases value <;> simp [EntryOf.mapPayload_id]
  cases store
  simp [StoreOf.mapPayload, identity]

theorem StoreOf.mapPayload_comp {Middle : Type v} {Target : Type w}
    (f : Payload → Middle) (g : Middle → Target) (store : StoreOf Payload) :
    (store.mapPayload f).mapPayload g = store.mapPayload (g ∘ f) := by
  simp [StoreOf.mapPayload, Array.map_map, Option.map_map,
    Function.comp_def, EntryOf.mapPayload_comp]

/-- A payload representation with a left inverse loses no store content or identity. -/
theorem StoreOf.mapPayload_roundtrip {Target : Type v}
    (encode : Payload → Target) (decode : Target → Payload)
    (faithful : ∀ payload, decode (encode payload) = payload) (store : StoreOf Payload) :
    (store.mapPayload encode).mapPayload decode = store := by
  rw [StoreOf.mapPayload_comp]
  have composite : decode ∘ encode = id := funext faithful
  rw [composite, StoreOf.mapPayload_id]

/-- Mapping preserves the allocator invariant in both directions. -/
theorem wellFormed_mapPayload_iff {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) : WellFormed (store.mapPayload f) ↔ WellFormed store := by
  constructor
  · intro valid handle entry present
    exact valid handle (entry.mapPayload f) (by simp [present])
  · intro valid handle mapped present
    rw [frameAt_mapPayload] at present
    obtain ⟨entry, before, rfl⟩ := Option.map_eq_some_iff.mp present
    exact valid handle entry before

/-- Even an information-losing payload map preserves invalid versus valid references. -/
theorem lookup_mapPayload_isSome {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (ref : Ref) :
    (lookup (store.mapPayload f) ref).isSome = (lookup store ref).isSome := by
  rw [lookup_mapPayload]
  simp

/-- An unbound valid slot remains unbound, independently of the payload map. -/
theorem lookup_mapPayload_unbound_iff {Target : Type v} (f : Payload → Target)
    (store : StoreOf Payload) (ref : Ref) :
    lookup (store.mapPayload f) ref = some none ↔ lookup store ref = some none := by
  rw [lookup_mapPayload]
  cases lookup store ref with
  | none => simp
  | some value => cases value <;> simp

/-! ## Concrete canaries

These exercise two slots and two handles, failed writes, handle reuse, and a
discarded speculative generation. All computation is checked by the kernel.
-/

private def sampleFrame : Frame := ["x", "y"]

private def sampleEnv : FrameEnv sampleFrame :=
  fun slot => if slot.val = 0 then some (.symbol "before") else none

private def sampleInitial : Store :=
  install (empty 2) ⟨0, by decide⟩ sampleFrame sampleEnv

private def sampleSpeculative : Store :=
  install sampleInitial ⟨0, by decide⟩ sampleFrame (fun _ => some (.symbol "speculative"))

private def sampleRestored : Store := rollback sampleSpeculative sampleInitial

private def sampleReallocated : Store :=
  install sampleRestored ⟨0, by decide⟩ sampleFrame (fun _ => some (.symbol "new"))

theorem canary_bound_value :
    lookup sampleInitial ⟨0, 0, 0⟩ = some (some (.symbol "before")) := by decide

theorem canary_unbound_is_valid : lookup sampleInitial ⟨0, 0, 1⟩ = some none := by decide

theorem canary_missing_handle : lookup sampleInitial ⟨1, 0, 0⟩ = none := by decide

theorem canary_invalid_slot : lookup sampleInitial ⟨0, 0, 2⟩ = none := by decide

theorem canary_write_changes_value :
    (write? sampleInitial ⟨0, 0, 0⟩ (some (.symbol "after"))).map
      (fun next => lookup next ⟨0, 0, 0⟩) = some (some (some (.symbol "after"))) := by decide

theorem canary_write_preserves_other_slot :
    (write? sampleInitial ⟨0, 0, 0⟩ (some (.symbol "after"))).map
      (fun next => lookup next ⟨0, 0, 1⟩) = some (some none) := by decide

theorem canary_write_clears_value :
    (write? sampleInitial ⟨0, 0, 0⟩ none).map
      (fun next => lookup next ⟨0, 0, 0⟩) = some (some none) := by decide

theorem canary_stale_write_rejected :
    (write? sampleSpeculative ⟨0, 0, 0⟩ (some (.symbol "wrong"))).isSome = false := by decide

theorem canary_invalid_slot_write_rejected :
    (write? sampleInitial ⟨0, 0, 2⟩ (some (.symbol "wrong"))).isSome = false := by decide

theorem canary_second_handle_preserves_first :
    lookup (install sampleInitial ⟨1, by decide⟩ sampleFrame
      (fun _ => some (.symbol "second"))) ⟨0, 0, 0⟩ =
        some (some (.symbol "before")) := by decide

theorem canary_reuse_rejects_old_generation :
    lookup sampleSpeculative ⟨0, 0, 0⟩ = none := by decide

theorem canary_rollback_restores_old_value :
    lookup sampleRestored ⟨0, 0, 0⟩ = some (some (.symbol "before")) := by decide

theorem canary_rollback_discards_speculative_generation :
    lookup sampleRestored ⟨0, 1, 0⟩ = none := by decide

theorem canary_rollback_does_not_rewind_counter : sampleRestored.nextGeneration = 2 := by decide

theorem canary_reallocation_rejects_discarded_generation :
    lookup sampleReallocated ⟨0, 1, 0⟩ = none := by decide

theorem canary_reallocation_uses_fresh_generation :
    lookup sampleReallocated ⟨0, 2, 0⟩ = some (some (.symbol "new")) := by decide

/-- The same coordinates in an independent store can denote a different value:
the caller must retain the owning store lineage along with an escaped reference. -/
theorem canary_coordinates_require_owner :
    lookup sampleInitial ⟨0, 0, 0⟩ ≠
      lookup (install (empty 2) ⟨0, by decide⟩ sampleFrame
        (fun _ => some (.symbol "foreign"))) ⟨0, 0, 0⟩ := by decide

theorem canary_execution_wellFormed : WellFormed sampleReallocated := by
  apply install_wellFormed
  apply rollback_wellFormed
  · exact install_wellFormed (empty_wellFormed 2) _ _ _
  · decide

/-- A future snapshot cannot be installed into an earlier allocation history. -/
theorem canary_future_snapshot_breaks_invariant :
    ¬ WellFormed (rollback (empty 2) sampleInitial) := by
  intro valid
  have impossible := valid 0 (EntryOf.initial 0 sampleFrame sampleEnv) (by
    simp [rollback, frameAt, sampleInitial, install, empty, StoreOf.empty])
  exact Nat.not_lt_zero _ impossible

/-! ## A shared finite-generation allocator

`Shared.Allocator` is one identity authority shared by all branch images.
Owner counts are manipulated by concrete checked retain/release operations.
They model a protocol, not a proof that runtime pointers follow that protocol.
The final release advances the handle's generation; an exhausted handle is
permanently unavailable. Branch rollback never rewinds this allocator.
-/

namespace Shared

structure Token where
  handle : Nat
  generation : Nat
  deriving DecidableEq, Repr

def Token.ref (token : Token) (slot : Nat) : Ref :=
  ⟨token.handle, token.generation, slot⟩

structure Cell where
  generation : Nat
  owners : Nat
  deriving DecidableEq, Repr

structure Allocator where
  cells : Array Cell
  generationBound : Nat
  deriving DecidableEq, Repr

def Allocator.empty (capacity generationBound : Nat) : Allocator :=
  ⟨Array.replicate capacity ⟨0, 0⟩, generationBound⟩

def Live (allocator : Allocator) (token : Token) : Prop :=
  match allocator.cells[token.handle]? with
  | some cell => cell.generation = token.generation ∧ 0 < cell.owners
  | none => False

instance (allocator : Allocator) (token : Token) : Decidable (Live allocator token) := by
  unfold Live
  split <;> infer_instance

def Retired (allocator : Allocator) (handle : Nat) : Prop :=
  match allocator.cells[handle]? with
  | some cell => cell.owners = 0 ∧ allocator.generationBound ≤ cell.generation
  | none => False

instance (allocator : Allocator) (handle : Nat) : Decidable (Retired allocator handle) := by
  unfold Retired
  split <;> infer_instance

/-- The finite bound permits its endpoint only for a retired, unowned cell. -/
def Allocator.WellFormed (allocator : Allocator) : Prop :=
  ∀ (handle : Nat) (cell : Cell), allocator.cells[handle]? = some cell →
    cell.generation ≤ allocator.generationBound ∧
      (0 < cell.owners → cell.generation < allocator.generationBound)

private def put (allocator : Allocator) (handle : Nat) (cell : Cell) : Allocator :=
  { allocator with cells := allocator.cells.setIfInBounds handle cell }

private theorem present_bound {allocator : Allocator} {handle : Nat} {cell : Cell}
    (present : allocator.cells[handle]? = some cell) : handle < allocator.cells.size := by
  obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp present
  exact bound

private theorem put_self {allocator : Allocator} {handle : Nat} {old : Cell}
    (present : allocator.cells[handle]? = some old) (cell : Cell) :
    (put allocator handle cell).cells[handle]? = some cell := by
  exact Array.getElem?_setIfInBounds_self_of_lt (present_bound present)

private theorem put_other (allocator : Allocator) (handle other : Nat)
    (distinct : handle ≠ other) (cell : Cell) :
    (put allocator handle cell).cells[other]? = allocator.cells[other]? := by
  exact Array.getElem?_setIfInBounds_ne distinct

/-- Allocation cannot replace a live incarnation or wrap its generation. -/
def allocate? (allocator : Allocator) (handle : Nat) : Option (Allocator × Token) := do
  let cell ← allocator.cells[handle]?
  if cell.owners = 0 ∧ cell.generation < allocator.generationBound then
    some (put allocator handle { cell with owners := 1 }, ⟨handle, cell.generation⟩)
  else none

private def changeOwners? (allocator : Allocator) (token : Token)
    (change : Cell → Cell) : Option Allocator := do
  let cell ← allocator.cells[token.handle]?
  if cell.generation = token.generation ∧ 0 < cell.owners then
    some (put allocator token.handle (change cell))
  else none

/-- A retained branch or escaped owner shares the existing token. -/
def retain? (allocator : Allocator) (token : Token) : Option Allocator :=
  changeOwners? allocator token (fun cell => { cell with owners := cell.owners + 1 })

private def releasedCell (cell : Cell) : Cell :=
  if cell.owners = 1 then ⟨cell.generation + 1, 0⟩
  else { cell with owners := cell.owners - 1 }

def release? (allocator : Allocator) (token : Token) : Option Allocator :=
  changeOwners? allocator token releasedCell

private theorem live_witness {allocator : Allocator} {token : Token}
    (live : Live allocator token) :
    ∃ cell, allocator.cells[token.handle]? = some cell ∧
      cell.generation = token.generation ∧ 0 < cell.owners := by
  cases present : allocator.cells[token.handle]? with
  | none => simp [Live, present] at live
  | some cell => exact ⟨cell, rfl, by simpa [Live, present] using live⟩

private theorem allocate_success {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    ∃ cell, allocator.cells[handle]? = some cell ∧ cell.owners = 0 ∧
      cell.generation < allocator.generationBound ∧
      next = put allocator handle { cell with owners := 1 } ∧
      token = ⟨handle, cell.generation⟩ := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, present] at allocated
  | some cell =>
    simp only [allocate?, present] at allocated
    change (if cell.owners = 0 ∧ cell.generation < allocator.generationBound then
      some (put allocator handle { cell with owners := 1 }, ⟨handle, cell.generation⟩)
      else none) = some (next, token) at allocated
    split at allocated
    · next valid =>
      obtain ⟨stateEq, tokenEq⟩ := Prod.mk.inj (Option.some.inj allocated)
      exact ⟨cell, rfl, valid.1, valid.2, stateEq.symm, tokenEq.symm⟩
    · simp at allocated

private theorem changeOwners_success {allocator next : Allocator} {token : Token}
    {change : Cell → Cell} (changed : changeOwners? allocator token change = some next) :
    ∃ cell, allocator.cells[token.handle]? = some cell ∧
      cell.generation = token.generation ∧ 0 < cell.owners ∧
      next = put allocator token.handle (change cell) := by
  cases present : allocator.cells[token.handle]? with
  | none => simp [changeOwners?, present] at changed
  | some cell =>
    simp only [changeOwners?, present] at changed
    change (if cell.generation = token.generation ∧ 0 < cell.owners then
      some (put allocator token.handle (change cell)) else none) = some next at changed
    split at changed
    · next valid =>
      exact ⟨cell, rfl, valid.1, valid.2, (Option.some.inj changed).symm⟩
    · simp at changed

theorem allocated_live {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) : Live next token := by
  obtain ⟨cell, present, _, _, rfl, rfl⟩ := allocate_success allocated
  simp [Live, put_self present]

/-- Distinct live tokens must occupy distinct handles in the shared authority. -/
theorem live_handle_unique {allocator : Allocator} {left right : Token}
    (leftLive : Live allocator left) (rightLive : Live allocator right)
    (sameHandle : left.handle = right.handle) : left = right := by
  obtain ⟨leftCell, leftPresent, leftGeneration, _⟩ := live_witness leftLive
  obtain ⟨rightCell, rightPresent, rightGeneration, _⟩ := live_witness rightLive
  rw [← sameHandle, leftPresent] at rightPresent
  cases Option.some.inj rightPresent
  cases left
  cases right
  simp_all

theorem live_prevents_allocation {allocator : Allocator} {token : Token}
    (live : Live allocator token) : allocate? allocator token.handle = none := by
  obtain ⟨cell, present, _, owned⟩ := live_witness live
  simp [allocate?, present, Nat.ne_of_gt owned]

/-- A new allocation cannot use any handle that was live immediately beforehand. -/
theorem fresh_allocation_distinct_handle {allocator next : Allocator} {handle : Nat}
    {fresh old : Token} (allocated : allocate? allocator handle = some (next, fresh))
    (oldLive : Live allocator old) : fresh.handle ≠ old.handle := by
  obtain ⟨_, _, _, _, _, rfl⟩ := allocate_success allocated
  intro same
  change handle = old.handle at same
  rw [same, live_prevents_allocation oldLive] at allocated
  contradiction

/-- A successful new allocation and every previously live allocation remain
simultaneously live with distinct handles and distinct tokens. Multiple owners
of one allocation intentionally share its token instead. -/
theorem allocation_separates_live {allocator next : Allocator} {handle : Nat}
    {fresh old : Token} (allocated : allocate? allocator handle = some (next, fresh))
    (oldLive : Live allocator old) :
    Live next fresh ∧ Live next old ∧ fresh.handle ≠ old.handle ∧ fresh ≠ old := by
  have distinct := fresh_allocation_distinct_handle allocated oldLive
  have freshLive := allocated_live allocated
  have oldStays : Live next old := by
    obtain ⟨cell, _, _, _, rfl, rfl⟩ := allocate_success allocated
    simpa [Live, put_other allocator handle old.handle distinct] using oldLive
  exact ⟨freshLive, oldStays, distinct, fun same => distinct (congrArg Token.handle same)⟩

theorem retired_prevents_allocation {allocator : Allocator} {handle : Nat}
    (retired : Retired allocator handle) : allocate? allocator handle = none := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, present]
  | some cell =>
    have bounds : allocator.generationBound ≤ cell.generation :=
      (by simpa [Retired, present] using retired :
        cell.owners = 0 ∧ allocator.generationBound ≤ cell.generation).2
    simp [allocate?, present, Nat.not_lt.mpr bounds]

theorem retain_live {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) : Live next token := by
  obtain ⟨cell, present, generation, _, rfl⟩ := changeOwners_success retained
  simp [Live, put_self present, generation]

theorem retain_increments_owners {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) :
    ∃ before after, allocator.cells[token.handle]? = some before ∧
      next.cells[token.handle]? = some after ∧
      after.generation = before.generation ∧ after.owners = before.owners + 1 := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success retained
  exact ⟨cell, _, present, put_self present _, rfl, rfl⟩

/-- Retention changes no token's validity, including invalid incarnations. -/
theorem retain_live_iff {allocator next : Allocator} {retained observed : Token}
    (success : retain? allocator retained = some next) :
    Live next observed ↔ Live allocator observed := by
  obtain ⟨cell, present, _, owned, rfl⟩ := changeOwners_success success
  by_cases same : retained.handle = observed.handle
  · unfold Live
    rw [← same]
    simp [put_self present, present, owned]
  · simp [Live, put_other allocator retained.handle observed.handle same]

theorem retain_preserves_live {allocator next : Allocator} {token other : Token}
    (live : Live allocator token) (retained : retain? allocator other = some next) :
    Live next token := (retain_live_iff retained).mpr live

theorem retain?_exists_iff_live (allocator : Allocator) (token : Token) :
    (∃ next, retain? allocator token = some next) ↔ Live allocator token := by
  constructor
  · rintro ⟨next, success⟩
    obtain ⟨cell, present, generation, owned, _⟩ := changeOwners_success success
    simp [Live, present, generation, owned]
  · intro live
    obtain ⟨cell, present, generation, owned⟩ := live_witness live
    exact ⟨put allocator token.handle { cell with owners := cell.owners + 1 }, by
      simp [retain?, changeOwners?, present, generation, owned]⟩

/-- A checked finite retain batch uses the existing monadic list fold. -/
def retainAll? (allocator : Allocator) (tokens : List Token) : Option Allocator :=
  tokens.foldlM (fun current token => retain? current token) allocator

@[simp] theorem retainAll?_nil (allocator : Allocator) :
    retainAll? allocator [] = some allocator := rfl

theorem retainAll?_cons (allocator : Allocator) (token : Token) (tokens : List Token) :
    retainAll? allocator (token :: tokens) =
      (retain? allocator token).bind (fun next => retainAll? next tokens) := by
  simp only [retainAll?, List.foldlM_cons, Option.bind_eq_bind]

private theorem retainAll?_cons_success {allocator next : Allocator}
    {token : Token} {tokens : List Token}
    (success : retainAll? allocator (token :: tokens) = some next) :
    ∃ middle, retain? allocator token = some middle ∧ retainAll? middle tokens = some next := by
  rw [retainAll?_cons] at success
  cases retained : retain? allocator token with
  | none => simp [retained] at success
  | some middle => exact ⟨middle, rfl, by simpa [retained] using success⟩

theorem retainAll?_live_iff {allocator next : Allocator} {tokens : List Token}
    (success : retainAll? allocator tokens = some next) (observed : Token) :
    Live next observed ↔ Live allocator observed := by
  induction tokens generalizing allocator with
  | nil =>
    simp only [retainAll?_nil, Option.some.injEq] at success
    subst next
    rfl
  | cons token tokens ih =>
    obtain ⟨middle, retained, rest⟩ := retainAll?_cons_success success
    exact (ih rest).trans (retain_live_iff retained)

/-- No earlier retain can repair a stale or unowned token later in the batch. -/
theorem retainAll?_exists_iff_live (allocator : Allocator) (tokens : List Token) :
    (∃ next, retainAll? allocator tokens = some next) ↔
      ∀ token ∈ tokens, Live allocator token := by
  induction tokens generalizing allocator with
  | nil => simp
  | cons token tokens ih =>
    constructor
    · rintro ⟨next, success⟩ observed member
      obtain ⟨middle, retained, rest⟩ := retainAll?_cons_success success
      rcases List.mem_cons.mp member with rfl | member
      · exact (retain?_exists_iff_live allocator observed).mp ⟨middle, retained⟩
      · exact (retain_live_iff retained).mp ((ih middle).mp ⟨next, rest⟩ observed member)
    · intro live
      obtain ⟨middle, retained⟩ := (retain?_exists_iff_live allocator token).mpr
        (live token (List.mem_cons_self ..))
      have restLive : ∀ observed ∈ tokens, Live middle observed := by
        intro observed member
        exact retain_preserves_live (live observed (List.mem_cons_of_mem _ member)) retained
      obtain ⟨next, rest⟩ := (ih middle).mpr restLive
      exact ⟨next, by simp [retainAll?_cons, retained, rest]⟩

private theorem retain_cells {allocator next : Allocator} {token : Token}
    (success : retain? allocator token = some next) (handle : Nat) :
    next.cells[handle]? = (allocator.cells[handle]?).map
      (fun cell => { cell with owners := cell.owners + if token.handle = handle then 1 else 0 }) := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success success
  by_cases same : token.handle = handle
  · subst handle
    simp [put_self present, present]
  · rw [put_other allocator token.handle handle same]
    cases allocator.cells[handle]? <;> simp [same]

/-- Checked batches preserve each generation and count every actual retain exactly. -/
theorem retainAll?_cells {allocator next : Allocator} {tokens : List Token}
    (success : retainAll? allocator tokens = some next) (handle : Nat) :
    next.cells[handle]? = (allocator.cells[handle]?).map
      (fun cell => { cell with owners := cell.owners + tokens.countP (fun token => token.handle == handle) }) := by
  induction tokens generalizing allocator with
  | nil =>
    simp only [retainAll?_nil, Option.some.injEq] at success
    subst next
    cases allocator.cells[handle]? <;> simp
  | cons token tokens ih =>
    obtain ⟨middle, retained, rest⟩ := retainAll?_cons_success success
    rw [ih rest, retain_cells retained]
    cases allocator.cells[handle]? <;> by_cases same : token.handle = handle <;>
      simp [same, Nat.add_assoc, Nat.add_comm]

/-- Strictly older incarnations are invalid even if their handle is currently owned. -/
theorem older_generation_not_live {allocator : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell)
    (older : token.generation < cell.generation) : ¬ Live allocator token := by
  simp [Live, present, Nat.ne_of_gt older]

/-- Generation progress is defined independently of token validity. -/
def GenerationsLE (before after : Allocator) : Prop :=
  ∀ (handle : Nat) (cell : Cell), before.cells[handle]? = some cell →
    ∃ next : Cell, after.cells[handle]? = some next ∧ cell.generation ≤ next.generation

private theorem put_generationsLE {allocator : Allocator} {handle : Nat} {old : Cell}
    (present : allocator.cells[handle]? = some old) (cell : Cell)
    (monotone : old.generation ≤ cell.generation) :
    GenerationsLE allocator (put allocator handle cell) := by
  intro other before beforePresent
  by_cases same : handle = other
  · subst other
    rw [present] at beforePresent
    cases Option.some.inj beforePresent
    exact ⟨cell, put_self present cell, monotone⟩
  · exact ⟨before, by rw [put_other allocator handle other same]; exact beforePresent,
      Nat.le_refl _⟩

theorem allocate_generationsLE {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl, _⟩ := allocate_success allocated
  exact put_generationsLE present _ (Nat.le_refl _)

theorem retain_generationsLE {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) : GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success retained
  exact put_generationsLE present _ (Nat.le_refl _)

theorem release_generationsLE {allocator next : Allocator} {token : Token}
    (released : release? allocator token = some next) : GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success released
  apply put_generationsLE present
  simp only [releasedCell]
  split <;> simp

/-- Only successful operations advance a shared allocator trace. -/
inductive Step : Allocator → Allocator → Prop where
  | allocate {before after : Allocator} {handle : Nat} {token : Token}
      (success : allocate? before handle = some (after, token)) : Step before after
  | retain {before after : Allocator} {token : Token}
      (success : retain? before token = some after) : Step before after
  | release {before after : Allocator} {token : Token}
      (success : release? before token = some after) : Step before after

inductive Trace : Allocator → Allocator → Prop where
  | refl (allocator : Allocator) : Trace allocator allocator
  | next {before middle after : Allocator} (history : Trace before middle)
      (step : Step middle after) : Trace before after

theorem Trace.trans {first middle last : Allocator}
    (before : Trace first middle) (after : Trace middle last) : Trace first last := by
  induction after with
  | refl => exact before
  | next _ step ih => exact .next ih step

/-- Every successful batch is a trace of the existing checked retain operation. -/
theorem retainAll?_trace {allocator next : Allocator} {tokens : List Token}
    (success : retainAll? allocator tokens = some next) : Trace allocator next := by
  induction tokens generalizing allocator with
  | nil =>
    simp only [retainAll?_nil, Option.some.injEq] at success
    subst next
    exact .refl _
  | cons token tokens ih =>
    obtain ⟨middle, retained, rest⟩ := retainAll?_cons_success success
    exact Trace.trans (.next (.refl _) (.retain retained)) (ih rest)

theorem Step.generationsLE {before after : Allocator} (step : Step before after) :
    GenerationsLE before after := by
  cases step with
  | allocate success => exact allocate_generationsLE success
  | retain success => exact retain_generationsLE success
  | release success => exact release_generationsLE success

theorem Trace.generationsLE {before after : Allocator} (trace : Trace before after) :
    GenerationsLE before after := by
  induction trace with
  | refl => exact fun _ cell present => ⟨cell, present, Nat.le_refl _⟩
  | next history step ih =>
    intro handle cell present
    obtain ⟨middle, middlePresent, first⟩ := ih handle cell present
    obtain ⟨last, lastPresent, second⟩ := step.generationsLE handle middle middlePresent
    exact ⟨last, lastPresent, Nat.le_trans first second⟩

/-- No sequence of allocation, retention, and release revives an old incarnation. -/
theorem stale_forever {before after : Allocator} {token : Token} {cell : Cell}
    (present : before.cells[token.handle]? = some cell)
    (older : token.generation < cell.generation) (trace : Trace before after) :
    ¬ Live after token := by
  obtain ⟨last, lastPresent, monotone⟩ := trace.generationsLE token.handle cell present
  exact older_generation_not_live lastPresent (Nat.lt_of_lt_of_le older monotone)

theorem final_release_advances {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (lastOwner : cell.owners = 1)
    (released : release? allocator token = some next) :
    next.cells[token.handle]? = some ⟨cell.generation + 1, 0⟩ := by
  obtain ⟨found, foundPresent, _, _, rfl⟩ := changeOwners_success released
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  simpa [releasedCell, lastOwner] using put_self present (releasedCell cell)

theorem final_release_never_revives {allocator released final : Allocator} {token : Token}
    {cell : Cell} (present : allocator.cells[token.handle]? = some cell)
    (lastOwner : cell.owners = 1) (success : release? allocator token = some released)
    (trace : Trace released final) : ¬ Live final token := by
  obtain ⟨found, foundPresent, generation, _, _⟩ := changeOwners_success success
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  apply stale_forever (final_release_advances present lastOwner success) _ trace
  simp [generation]

theorem release_shared_stays_live {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (shared : 1 < cell.owners)
    (released : release? allocator token = some next) : Live next token := by
  obtain ⟨found, foundPresent, generation, _, rfl⟩ := changeOwners_success released
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  have notLast : cell.owners ≠ 1 := Nat.ne_of_gt shared
  have remaining : 0 < cell.owners - 1 := Nat.sub_pos_of_lt shared
  simp [Live, put_self present, releasedCell, notLast, generation, remaining]

private theorem put_wellFormed {allocator : Allocator} (valid : allocator.WellFormed)
    (handle : Nat) (cell : Cell) (bounded : cell.generation ≤ allocator.generationBound)
    (liveBound : 0 < cell.owners → cell.generation < allocator.generationBound) :
    (put allocator handle cell).WellFormed := by
  intro other found present
  by_cases same : handle = other
  · subst other
    by_cases inBounds : handle < allocator.cells.size
    · change (allocator.cells.setIfInBounds handle cell)[handle]? = some found at present
      rw [Array.getElem?_setIfInBounds_self_of_lt inBounds] at present
      cases Option.some.inj present
      exact ⟨bounded, liveBound⟩
    · have missing : (put allocator handle cell).cells[handle]? = none := by
        apply Array.getElem?_eq_none
        simpa [put] using Nat.not_lt.mp inBounds
      rw [missing] at present
      contradiction
  · rw [put_other allocator handle other same] at present
    exact valid other found present

theorem Allocator.empty_wellFormed (capacity generationBound : Nat) :
    (Allocator.empty capacity generationBound).WellFormed := by
  intro handle cell present
  obtain ⟨bound, cellEq⟩ := Array.getElem?_eq_some_iff.mp present
  have same : cell = ⟨0, 0⟩ := by simpa [Allocator.empty] using cellEq.symm
  subst cell
  simp [Allocator.empty]

theorem allocate_wellFormed {allocator next : Allocator} {handle : Nat} {token : Token}
    (valid : allocator.WellFormed)
    (allocated : allocate? allocator handle = some (next, token)) : next.WellFormed := by
  obtain ⟨cell, _, _, bound, rfl, _⟩ := allocate_success allocated
  exact put_wellFormed valid _ _ (Nat.le_of_lt bound) (fun _ => bound)

theorem retain_wellFormed {allocator next : Allocator} {token : Token}
    (valid : allocator.WellFormed) (retained : retain? allocator token = some next) :
    next.WellFormed := by
  obtain ⟨cell, present, _, owned, rfl⟩ := changeOwners_success retained
  have bounds := valid token.handle cell present
  exact put_wellFormed valid _ _ bounds.1 (fun _ => bounds.2 owned)

theorem release_wellFormed {allocator next : Allocator} {token : Token}
    (valid : allocator.WellFormed) (released : release? allocator token = some next) :
    next.WellFormed := by
  obtain ⟨cell, present, _, owned, rfl⟩ := changeOwners_success released
  have bounds := valid token.handle cell present
  by_cases lastOwner : cell.owners = 1
  · simp only [releasedCell, if_pos lastOwner]
    exact put_wellFormed valid _ _ (Nat.succ_le_of_lt (bounds.2 owned)) (by simp)
  · simp only [releasedCell, if_neg lastOwner]
    exact put_wellFormed valid _ _ bounds.1 (fun _ => bounds.2 owned)

theorem Step.wellFormed {before after : Allocator} (step : Step before after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases step with
  | allocate success => exact allocate_wellFormed valid success
  | retain success => exact retain_wellFormed valid success
  | release success => exact release_wellFormed valid success

theorem Trace.wellFormed {before after : Allocator} (trace : Trace before after)
    (valid : before.WellFormed) : after.WellFormed := by
  induction trace with
  | refl => exact valid
  | next history step ih => exact step.wellFormed ih

theorem Step.bound_eq {before after : Allocator} (step : Step before after) :
    after.generationBound = before.generationBound := by
  cases step with
  | allocate success =>
    obtain ⟨_, _, _, _, rfl, _⟩ := allocate_success success
    rfl
  | retain success =>
    obtain ⟨_, _, _, _, rfl⟩ := changeOwners_success success
    rfl
  | release success =>
    obtain ⟨_, _, _, _, rfl⟩ := changeOwners_success success
    rfl

theorem Trace.bound_eq {before after : Allocator} (trace : Trace before after) :
    after.generationBound = before.generationBound := by
  induction trace with
  | refl => rfl
  | next history step ih => exact step.bound_eq.trans ih

theorem retirement_permanent {before after : Allocator} {handle : Nat}
    (retired : Retired before handle) (trace : Trace before after) :
    allocate? after handle = none := by
  cases present : before.cells[handle]? with
  | none => simp [Retired, present] at retired
  | some cell =>
    have exhausted : before.generationBound ≤ cell.generation :=
      (by simpa [Retired, present] using retired :
        cell.owners = 0 ∧ before.generationBound ≤ cell.generation).2
    obtain ⟨last, lastPresent, monotone⟩ := trace.generationsLE handle cell present
    have exhaustedAfter : ¬ last.generation < after.generationBound := by
      rw [trace.bound_eq]
      exact Nat.not_lt.mpr (Nat.le_trans exhausted monotone)
    simp [allocate?, lastPresent, exhaustedAfter]

theorem allocated_generation_bounded {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    token.generation < allocator.generationBound := by
  obtain ⟨_, _, _, bound, _, rfl⟩ := allocate_success allocated
  exact bound

theorem final_generation_retires {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (lastOwner : cell.owners = 1)
    (lastGeneration : cell.generation + 1 = allocator.generationBound)
    (released : release? allocator token = some next) : Retired next token.handle := by
  have advanced := final_release_advances present lastOwner released
  have boundEq := (Step.release released).bound_eq
  simp [Retired, advanced, boundEq, lastGeneration]

/-! ## Branch values under a shared identity authority

An image has no allocation counter. Publishing uses a token from the shared
allocator; capturing one frame performs a checked retain and preserves its
original handle. Publication transfers an already-held owner into an image;
it does not mint another owner. Whole-image capture conservatively retains every present frame, including empty
inventories, before publishing the complete branch image. Payload references outside
that directory, arbitrary image destruction, and correspondence to actual runtime
pointers remain separate obligations.
-/

structure ImageOf (Payload : Type u) where
  entries : Array (Option (EntryOf Payload))
  writeClock : Nat

/-- Syntax-valued branch images retain the original API. -/
abbrev Image := ImageOf Atom

def ImageOf.empty (capacity : Nat) : ImageOf Payload := ⟨Array.replicate capacity none, 0⟩

private def ImageOf.toStore (image : ImageOf Payload) : StoreOf Payload :=
  ⟨image.entries, 0, image.writeClock⟩

def ImageOf.frameAt (image : ImageOf Payload) (handle : Nat) : Option (EntryOf Payload) :=
  MetavariableFrameStore.frameAt image.toStore handle

def ImageOf.lookup (image : ImageOf Payload) (ref : Ref) : Option (Option Payload) :=
  MetavariableFrameStore.lookup image.toStore ref

def ImageOf.readSlot? (image : ImageOf Payload) (ref : Ref) : Option (SlotReadbackOf Payload) :=
  MetavariableFrameStore.readSlot? image.toStore ref

/-- Raw slot inspection uses the same shared-identity licence as value lookup. -/
def ImageOf.readSlotOwned? (allocator : Allocator) (image : ImageOf Payload) (ref : Ref) :
    Option (SlotReadbackOf Payload) :=
  if Live allocator ⟨ref.handle, ref.generation⟩ then image.readSlot? ref else none

/-- Narrow assignments without removing frame inventories or clock history.
This pure projection transfers the current image; checked capture acquires
additional owners when another holder is published. -/
def ImageOf.projectSlots (image : ImageOf Payload) (keep : Nat → Nat → Bool) : ImageOf Payload :=
  ⟨Array.ofFn (fun handle : Fin image.entries.size =>
    (image.entries[handle]).map (fun entry => entry.projectSlots (keep handle.val))), image.writeClock⟩

theorem ImageOf.frameAt_projectSlots (image : ImageOf Payload) (keep : Nat → Nat → Bool) (handle : Nat) :
    (image.projectSlots keep).frameAt handle =
      (image.frameAt handle).map (fun entry => entry.projectSlots (keep handle)) := by
  simp only [ImageOf.frameAt, ImageOf.toStore, MetavariableFrameStore.frameAt, ImageOf.projectSlots]
  by_cases bound : handle < image.entries.size
  · simp [bound]
  · simp [bound]

/-- Observation checked against the shared authority, even for an old value image. -/
def ImageOf.lookupOwned (allocator : Allocator) (image : ImageOf Payload) (ref : Ref) : Option (Option Payload) :=
  if Live allocator ⟨ref.handle, ref.generation⟩ then image.lookup ref else none

def ImageOf.write? (image : ImageOf Payload) (ref : Ref) (value : Option Payload) : Option (ImageOf Payload) :=
  (MetavariableFrameStore.write? image.toStore ref value).map (fun store => ⟨store.entries, store.writeClock⟩)

def ImageOf.activate? (image : ImageOf Payload) (token : Token) : Option (ImageOf Payload) :=
  (MetavariableFrameStore.activate? image.toStore token.handle token.generation).map
    (fun store => ⟨store.entries, store.writeClock⟩)

/-- Publish a previously owned token without changing its handle or generation. -/
def ImageOf.publish? (allocator : Allocator) (image : ImageOf Payload) (token : Token)
    (frame : Frame) (env : FrameEnvOf Payload frame) : Option (ImageOf Payload) :=
  if Live allocator token ∧ token.handle < image.entries.size then
    some ⟨image.entries.setIfInBounds token.handle
      (some (EntryOf.initial token.generation frame env)), image.writeClock⟩
  else none

private def ImageOf.projectFrame (image : ImageOf Payload) (handle : Nat) (entry : EntryOf Payload) : ImageOf Payload :=
  ⟨(Array.replicate image.entries.size none).setIfInBounds handle (some entry), image.writeClock⟩

/-- Retain one selected frame and project it into a new branch at the same handle. -/
def ImageOf.capture? (allocator : Allocator) (image : ImageOf Payload) (token : Token) :
    Option (Allocator × ImageOf Payload) := do
  let entry ← image.frameAt token.handle
  if entry.generation = token.generation then
    match retain? allocator token with
    | some next => some (next, image.projectFrame token.handle entry)
    | none => none
  else none

/-- Every present frame occurs once, including frames with zero slots. -/
def ImageOf.inventory (image : ImageOf Payload) : List Token :=
  (List.range image.entries.size).filterMap fun handle =>
    (image.frameAt handle).map fun entry => ⟨handle, entry.generation⟩

@[simp] theorem ImageOf.mem_inventory (image : ImageOf Payload) (token : Token) :
    token ∈ image.inventory ↔
      ∃ entry, image.frameAt token.handle = some entry ∧ entry.generation = token.generation := by
  constructor
  · intro member
    obtain ⟨handle, _, mapped⟩ := List.mem_filterMap.mp member
    obtain ⟨entry, present, same⟩ := Option.map_eq_some_iff.mp mapped
    cases same
    exact ⟨entry, present, rfl⟩
  · rintro ⟨entry, present, generation⟩
    apply List.mem_filterMap.mpr
    refine ⟨token.handle, List.mem_range.mpr (frameAt_bound present), ?_⟩
    simp only [present, Option.map_some]
    cases token
    simp_all

private theorem ImageOf.inventory_handles (image : ImageOf Payload) :
    image.inventory.map Token.handle =
      (List.range image.entries.size).filter (fun handle => (image.frameAt handle).isSome) := by
  unfold ImageOf.inventory
  rw [List.map_filterMap]
  have pointwise :
      (fun handle => ((image.frameAt handle).map (fun entry => Token.mk handle entry.generation)).map Token.handle) =
        (fun handle => if (image.frameAt handle).isSome then some handle else none) := by
    funext handle
    cases image.frameAt handle <;> rfl
  rw [pointwise]
  simpa only [Option.guard] using congrFun
    (List.filterMap_eq_filter (p := fun handle => (image.frameAt handle).isSome))
    (List.range image.entries.size)

theorem ImageOf.inventory_handles_nodup (image : ImageOf Payload) :
    (image.inventory.map Token.handle).Nodup := by
  rw [ImageOf.inventory_handles]
  exact (List.nodup_range).filter _

private theorem ImageOf.inventory_count (image : ImageOf Payload) (handle : Nat)
    {entry : EntryOf Payload} (present : image.frameAt handle = some entry) :
    image.inventory.countP (fun token => token.handle == handle) = 1 := by
  have member : handle ∈ image.inventory.map Token.handle := List.mem_map.mpr
    ⟨⟨handle, entry.generation⟩, (ImageOf.mem_inventory image _).mpr ⟨entry, present, rfl⟩, rfl⟩
  have count := (image.inventory_handles_nodup).count (a := handle)
  simpa only [List.count, List.countP_map, Function.comp_def, Bool.beq_comm,
    if_pos member] using count

/-- Publish a complete immutable image only after every present token is retained.
Failed prefixes remain internal to the checked fold; no partial image or allocator
is returned. This is a functional ownership protocol, not a C mutation theorem. -/
def ImageOf.captureAll? (allocator : Allocator) (image : ImageOf Payload) :
    Option (Allocator × ImageOf Payload) :=
  match retainAll? allocator image.inventory with
  | some next => some (next, image)
  | none => none

private theorem ImageOf.captureAll_success {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) :
    retainAll? allocator image.inventory = some next ∧ captured = image := by
  cases retained : retainAll? allocator image.inventory with
  | none => simp [ImageOf.captureAll?, retained] at success
  | some result =>
    have same : result = next ∧ image = captured := by
      simpa [ImageOf.captureAll?, retained] using success
    exact ⟨congrArg some same.1, same.2.symm⟩

theorem ImageOf.captureAll_preserves_image {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) : captured = image :=
  (ImageOf.captureAll_success success).2

/-- Successful whole capture covers exactly the actual present-frame guards. -/
theorem ImageOf.captureAll?_exists_iff_live (allocator : Allocator) (image : ImageOf Payload) :
    (∃ next captured, image.captureAll? allocator = some (next, captured)) ↔
      ∀ token ∈ image.inventory, Live allocator token := by
  constructor
  · rintro ⟨next, captured, success⟩
    exact (retainAll?_exists_iff_live allocator image.inventory).mp
      ⟨next, (ImageOf.captureAll_success success).1⟩
  · intro live
    obtain ⟨next, retained⟩ := (retainAll?_exists_iff_live allocator image.inventory).mpr live
    exact ⟨next, image, by simp [ImageOf.captureAll?, retained]⟩

theorem ImageOf.captureAll_preserves_frameAt {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) (handle : Nat) :
    captured.frameAt handle = image.frameAt handle := by
  rw [ImageOf.captureAll_preserves_image success]

theorem ImageOf.captureAll_preserves_lookup {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) (ref : Ref) :
    captured.lookup ref = image.lookup ref := by
  rw [(ImageOf.captureAll_success success).2]

theorem ImageOf.captureAll_preserves_readSlot {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) (ref : Ref) :
    captured.readSlot? ref = image.readSlot? ref := by
  rw [ImageOf.captureAll_preserves_image success]

theorem ImageOf.captureAll_preserves_clock {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) :
    captured.writeClock = image.writeClock := by
  rw [ImageOf.captureAll_preserves_image success]

theorem ImageOf.captureAll_live {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured))
    (token : Token) (member : token ∈ image.inventory) : Live next token := by
  have retained := (ImageOf.captureAll_success success).1
  have live := (retainAll?_exists_iff_live allocator image.inventory).mp ⟨next, retained⟩ token member
  exact (retainAll?_live_iff retained token).mpr live

theorem ImageOf.captureAll_trace {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) : Trace allocator next :=
  retainAll?_trace (ImageOf.captureAll_success success).1

/-- Each actual inventory frame gains precisely one owner at the same generation. -/
theorem ImageOf.captureAll_retains_owner {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured))
    {handle : Nat} {entry : EntryOf Payload} (present : image.frameAt handle = some entry) :
    ∃ before after, allocator.cells[handle]? = some before ∧ next.cells[handle]? = some after ∧
      before.generation = entry.generation ∧ after.generation = entry.generation ∧
      after.owners = before.owners + 1 := by
  have retained := (ImageOf.captureAll_success success).1
  have live := (retainAll?_exists_iff_live allocator image.inventory).mp ⟨next, retained⟩
    ⟨handle, entry.generation⟩ ((ImageOf.mem_inventory image _).mpr ⟨entry, present, rfl⟩)
  obtain ⟨before, beforePresent, generation, _⟩ := live_witness live
  refine ⟨before, { before with owners := before.owners + 1 }, beforePresent, ?_, generation, generation, rfl⟩
  simpa [beforePresent, ImageOf.inventory_count image handle present] using retainAll?_cells retained handle

/-- Stale authority anywhere in the inventory refuses the complete capture. -/
theorem ImageOf.captureAll?_stale (allocator : Allocator) (image : ImageOf Payload)
    (token : Token) (member : token ∈ image.inventory) (stale : ¬ Live allocator token) :
    image.captureAll? allocator = none := by
  cases retained : retainAll? allocator image.inventory with
  | none => simp [ImageOf.captureAll?, retained]
  | some next =>
    exact False.elim (stale ((retainAll?_exists_iff_live allocator image.inventory).mp ⟨next, retained⟩ token member))

/-- Full-inventory authority preserves every lookup, including invalid and unbound slots. -/
theorem ImageOf.lookupOwned_eq_lookup (allocator : Allocator) (image : ImageOf Payload)
    (live : ∀ token ∈ image.inventory, Live allocator token) (ref : Ref) :
    image.lookupOwned allocator ref = image.lookup ref := by
  cases present : image.frameAt ref.handle with
  | none =>
    have absent : image.lookup ref = none := by
      change MetavariableFrameStore.lookup image.toStore ref = none
      change MetavariableFrameStore.frameAt image.toStore ref.handle = none at present
      simp [MetavariableFrameStore.lookup, present]
    simp [ImageOf.lookupOwned, absent]
  | some entry =>
    by_cases generation : entry.generation = ref.generation
    · have tokenLive := live ⟨ref.handle, ref.generation⟩
        ((ImageOf.mem_inventory image _).mpr ⟨entry, present, generation⟩)
      simp [ImageOf.lookupOwned, tokenLive]
    · have absent : image.lookup ref = none := lookup_stale present generation
      simp [ImageOf.lookupOwned, absent]

theorem ImageOf.captureAll_lookupOwned {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) (ref : Ref) :
    captured.lookupOwned next ref = image.lookup ref := by
  rw [(ImageOf.captureAll_success success).2]
  exact image.lookupOwned_eq_lookup next (ImageOf.captureAll_live success) ref

theorem ImageOf.readSlotOwned?_eq_readSlot (allocator : Allocator) (image : ImageOf Payload)
    (live : ∀ token ∈ image.inventory, Live allocator token) (ref : Ref) :
    image.readSlotOwned? allocator ref = image.readSlot? ref := by
  cases present : image.frameAt ref.handle with
  | none =>
    have absent : image.readSlot? ref = none := by
      change MetavariableFrameStore.readSlot? image.toStore ref = none
      change MetavariableFrameStore.frameAt image.toStore ref.handle = none at present
      simp [MetavariableFrameStore.readSlot?, present]
    simp [ImageOf.readSlotOwned?, absent]
  | some entry =>
    by_cases generation : entry.generation = ref.generation
    · have tokenLive := live ⟨ref.handle, ref.generation⟩
        ((ImageOf.mem_inventory image _).mpr ⟨entry, present, generation⟩)
      simp [ImageOf.readSlotOwned?, tokenLive]
    · have absent : image.readSlot? ref = none :=
        MetavariableFrameStore.readSlot?_stale (store := image.toStore) present generation
      simp [ImageOf.readSlotOwned?, absent]

theorem ImageOf.captureAll_readSlotOwned {allocator next : Allocator}
    {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured)) (ref : Ref) :
    captured.readSlotOwned? next ref = image.readSlot? ref := by
  rw [ImageOf.captureAll_preserves_image success]
  exact image.readSlotOwned?_eq_readSlot next (ImageOf.captureAll_live success) ref

/-- The original syntax-valued construction specializes the common carrier. -/
abbrev Image.empty (capacity : Nat) : Image := ImageOf.empty capacity
abbrev Image.frameAt (image : Image) (handle : Nat) := ImageOf.frameAt image handle
abbrev Image.lookup (image : Image) (ref : Ref) := ImageOf.lookup image ref
abbrev Image.lookupOwned (allocator : Allocator) (image : Image) (ref : Ref) :=
  ImageOf.lookupOwned allocator image ref
abbrev Image.write? (image : Image) (ref : Ref) (value : Option Atom) :=
  ImageOf.write? image ref value
abbrev Image.publish? (allocator : Allocator) (image : Image) (token : Token)
    (frame : Frame) (env : FrameEnv frame) :=
  ImageOf.publish? allocator image token frame env
abbrev Image.capture? (allocator : Allocator) (image : Image) (token : Token) :=
  ImageOf.capture? allocator image token
abbrev Image.captureAll? (allocator : Allocator) (image : Image) :=
  ImageOf.captureAll? allocator image

/-- Transport payloads in a branch without changing its identity directory. -/
def ImageOf.mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) : ImageOf Target :=
  ⟨image.entries.map (Option.map (EntryOf.mapPayload f)), image.writeClock⟩

private theorem ImageOf.toStore_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) :
    (image.mapPayload f).toStore = image.toStore.mapPayload f := rfl

@[simp] theorem ImageOf.frameAt_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (handle : Nat) :
    (image.mapPayload f).frameAt handle = (image.frameAt handle).map (EntryOf.mapPayload f) :=
  MetavariableFrameStore.frameAt_mapPayload f image.toStore handle

@[simp] theorem ImageOf.inventory_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) : (image.mapPayload f).inventory = image.inventory := by
  have sizeEq : (image.mapPayload f).entries.size = image.entries.size := Array.size_map
  simp only [ImageOf.inventory, sizeEq, ImageOf.frameAt_mapPayload, Option.map_map]
  rfl

/-- Whole-image ownership transport depends on identities, independently of payloads. -/
theorem ImageOf.captureAll?_mapPayload {Target : Type v} (f : Payload → Target)
    (allocator : Allocator) (image : ImageOf Payload) :
    (image.mapPayload f).captureAll? allocator =
      (image.captureAll? allocator).map (fun result => (result.1, result.2.mapPayload f)) := by
  simp only [ImageOf.captureAll?, ImageOf.inventory_mapPayload]
  cases retainAll? allocator image.inventory <;> rfl

@[simp] theorem ImageOf.lookup_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (ref : Ref) :
    (image.mapPayload f).lookup ref = (image.lookup ref).map (Option.map f) :=
  MetavariableFrameStore.lookup_mapPayload f image.toStore ref

@[simp] theorem ImageOf.readSlot?_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (ref : Ref) :
    (image.mapPayload f).readSlot? ref = (image.readSlot? ref).map (SlotReadbackOf.mapPayload f) :=
  MetavariableFrameStore.readSlot?_mapPayload f image.toStore ref

@[simp] theorem ImageOf.readSlotOwned?_mapPayload {Target : Type v} (f : Payload → Target)
    (allocator : Allocator) (image : ImageOf Payload) (ref : Ref) :
    (image.mapPayload f).readSlotOwned? allocator ref =
      (image.readSlotOwned? allocator ref).map (SlotReadbackOf.mapPayload f) := by
  unfold ImageOf.readSlotOwned?
  split <;> simp

theorem ImageOf.activate?_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (token : Token) :
    (image.mapPayload f).activate? token =
      (image.activate? token).map (ImageOf.mapPayload f) := by
  unfold ImageOf.activate?
  rw [ImageOf.toStore_mapPayload, MetavariableFrameStore.activate?_mapPayload]
  cases MetavariableFrameStore.activate? image.toStore token.handle token.generation <;> rfl

@[simp] theorem ImageOf.lookupOwned_mapPayload {Target : Type v} (f : Payload → Target)
    (allocator : Allocator) (image : ImageOf Payload) (ref : Ref) :
    (image.mapPayload f).lookupOwned allocator ref =
      (image.lookupOwned allocator ref).map (Option.map f) := by
  unfold ImageOf.lookupOwned
  split <;> simp

theorem ImageOf.write?_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (ref : Ref) (value : Option Payload) :
    (image.mapPayload f).write? ref (value.map f) =
      (image.write? ref value).map (ImageOf.mapPayload f) := by
  unfold ImageOf.write?
  rw [ImageOf.toStore_mapPayload, MetavariableFrameStore.write?_mapPayload]
  cases MetavariableFrameStore.write? image.toStore ref value <;> rfl

theorem ImageOf.publish?_mapPayload {Target : Type v} (f : Payload → Target)
    (allocator : Allocator) (image : ImageOf Payload) (token : Token)
    (frame : Frame) (env : FrameEnvOf Payload frame) :
    (image.mapPayload f).publish? allocator token frame (MetavariableFrame.mapPayload f env) =
      (image.publish? allocator token frame env).map (ImageOf.mapPayload f) := by
  simp [ImageOf.publish?, ImageOf.mapPayload, EntryOf.mapPayload, EntryOf.initial,
    Array.map_ofFn]
  rfl

private theorem ImageOf.projectFrame_mapPayload {Target : Type v} (f : Payload → Target)
    (image : ImageOf Payload) (handle : Nat) (entry : EntryOf Payload) :
    (image.projectFrame handle entry).mapPayload f =
      (image.mapPayload f).projectFrame handle (entry.mapPayload f) := by
  simp [ImageOf.projectFrame, ImageOf.mapPayload]

/-- Capture preserves both the transported frame and the exact allocator result. -/
theorem ImageOf.capture?_mapPayload {Target : Type v} (f : Payload → Target)
    (allocator : Allocator) (image : ImageOf Payload) (token : Token) :
    (image.mapPayload f).capture? allocator token =
      (image.capture? allocator token).map (fun result => (result.1, result.2.mapPayload f)) := by
  unfold ImageOf.capture?
  rw [ImageOf.frameAt_mapPayload]
  cases image.frameAt token.handle with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    change (if entry.generation = token.generation then
      match retain? allocator token with
      | some next => some (next, (image.mapPayload f).projectFrame token.handle (entry.mapPayload f))
      | none => none else none) = _
    split
    · cases retain? allocator token <;> simp_all [ImageOf.projectFrame_mapPayload]
    · simp_all

theorem Image.lookup_publish {allocator : Allocator} {image result : ImageOf Payload}
    {token : Token} {frame : Frame} {env : FrameEnvOf Payload frame}
    (published : image.publish? allocator token frame env = some result) (slot : Slot frame) :
    result.lookup (token.ref slot.val) = some (env slot) := by
  unfold ImageOf.publish? at published
  split at published
  · next valid =>
    cases Option.some.inj published
    simp [ImageOf.lookup, ImageOf.toStore, Token.ref, EntryOf.initial,
      MetavariableFrameStore.lookup, MetavariableFrameStore.frameAt,
      Array.getElem?_setIfInBounds_self_of_lt valid.2, slot.isLt]
  · simp at published

theorem Image.lookup_write {image next : ImageOf Payload} {ref : Ref} {value : Option Payload}
    (written : image.write? ref value = some next) : next.lookup ref = some value := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    simpa [ImageOf.lookup, ImageOf.toStore, MetavariableFrameStore.lookup, MetavariableFrameStore.frameAt] using
      MetavariableFrameStore.lookup_write result

/-- A branch write changes only the selected coordinates for every payload type. -/
theorem ImageOf.lookup_write_other {image next : ImageOf Payload} {ref other : Ref}
    {value : Option Payload} (written : image.write? ref value = some next)
    (distinct : other ≠ ref) : next.lookup other = image.lookup other := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    simpa [ImageOf.lookup, ImageOf.toStore, MetavariableFrameStore.lookup,
      MetavariableFrameStore.frameAt] using
      MetavariableFrameStore.lookup_write_other result distinct

theorem Image.write_preserves_identity {image next : ImageOf Payload} {ref : Ref} {value : Option Payload}
    (written : image.write? ref value = some next) :
    ∃ before after, image.frameAt ref.handle = some before ∧
      next.frameAt ref.handle = some after ∧
      before.generation = ref.generation ∧ after.generation = ref.generation := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    obtain ⟨entry, present, generation, _, rfl⟩ := write?_success result
    refine ⟨entry, updateEntry entry ref.slot value (image.writeClock + 1), present, ?_, generation, generation⟩
    simpa [ImageOf.frameAt, ImageOf.toStore, MetavariableFrameStore.frameAt, replace] using
      frameAt_replace_self image.toStore ref.handle (frameAt_bound present)
        (updateEntry entry ref.slot value (image.writeClock + 1))

theorem ImageOf.write_advances_clock {image next : ImageOf Payload} {ref : Ref} {value : Option Payload}
    (written : image.write? ref value = some next) : next.writeClock = image.writeClock + 1 := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    exact MetavariableFrameStore.write_advances_clock result

private theorem Image.capture_success {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ entry, image.frameAt token.handle = some entry ∧
      entry.generation = token.generation ∧ retain? allocator token = some next ∧
      captured = image.projectFrame token.handle entry := by
  cases present : image.frameAt token.handle with
  | none => simp [ImageOf.capture?, present] at success
  | some entry =>
    by_cases generation : entry.generation = token.generation
    · cases retained : retain? allocator token with
      | none => simp [ImageOf.capture?, present, retained] at success
      | some after =>
        have equal : after = next ∧ image.projectFrame token.handle entry = captured := by
          simpa [ImageOf.capture?, present, generation, retained] using success
        exact ⟨entry, rfl, generation, congrArg some equal.1, equal.2.symm⟩
    · simp [ImageOf.capture?, present, generation] at success

theorem Image.capture_retains_owner {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ before after, allocator.cells[token.handle]? = some before ∧
      next.cells[token.handle]? = some after ∧
      after.generation = before.generation ∧ after.owners = before.owners + 1 := by
  obtain ⟨_, _, _, retained, _⟩ := Image.capture_success success
  exact retain_increments_owners retained

theorem Image.capture_live {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    Live next token := by
  obtain ⟨_, _, _, retained, _⟩ := Image.capture_success success
  exact retain_live retained

theorem Image.capture_preserves_identity {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ entry, image.frameAt token.handle = some entry ∧
      captured.frameAt token.handle = some entry ∧ entry.generation = token.generation := by
  obtain ⟨entry, present, generation, _, rfl⟩ := Image.capture_success success
  refine ⟨entry, present, ?_, generation⟩
  have bound : token.handle < image.entries.size := frameAt_bound present
  simp [ImageOf.frameAt, ImageOf.projectFrame, ImageOf.toStore, MetavariableFrameStore.frameAt, bound]

theorem Image.capture_preserves_lookup {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured))
    (slot : Nat) : captured.lookup (token.ref slot) = image.lookup (token.ref slot) := by
  obtain ⟨entry, before, after, generation⟩ := Image.capture_preserves_identity success
  have first := lookup_of_frameAt (ref := token.ref slot) before generation
  have second := lookup_of_frameAt (ref := token.ref slot) after generation
  exact second.trans first.symm

theorem ImageOf.capture_preserves_clock {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    captured.writeClock = image.writeClock := by
  obtain ⟨_, _, _, _, rfl⟩ := Image.capture_success success
  rfl

/-- Selected-frame capture keeps its complete metadata and directory clock,
independently of whether any of its slots is bound. -/
theorem ImageOf.capture_preserves_readSlot {allocator next : Allocator} {image captured : ImageOf Payload}
    {token : Token} (success : image.capture? allocator token = some (next, captured))
    (slot : Nat) : captured.readSlot? (token.ref slot) = image.readSlot? (token.ref slot) := by
  have clock := ImageOf.capture_preserves_clock success
  obtain ⟨entry, before, after, generation⟩ := Image.capture_preserves_identity success
  change MetavariableFrameStore.readSlot? captured.toStore (token.ref slot) =
    MetavariableFrameStore.readSlot? image.toStore (token.ref slot)
  rw [MetavariableFrameStore.readSlot?_of_frameAt
      (store := captured.toStore) (ref := token.ref slot) after generation,
    MetavariableFrameStore.readSlot?_of_frameAt
      (store := image.toStore) (ref := token.ref slot) before generation]
  exact congrArg (fun reading => entry.readSlot? reading slot) clock

theorem Image.stale_owned_lookup {before after : Allocator} {token : Token} {cell : Cell}
    (present : before.cells[token.handle]? = some cell) (older : token.generation < cell.generation)
    (trace : Trace before after) (image : ImageOf Payload) (slot : Nat) :
    image.lookupOwned after (token.ref slot) = none := by
  have stale := stale_forever present older trace
  change (if Live after token then image.lookup (token.ref slot) else none) = none
  exact if_neg stale

theorem ImageOf.mapPayload_id (image : ImageOf Payload) :
    image.mapPayload id = image := by
  have identity : Option.map (EntryOf.mapPayload (Payload := Payload) id) = id := by
    funext value
    cases value <;> simp [EntryOf.mapPayload_id]
  cases image
  simp [ImageOf.mapPayload, identity]

theorem ImageOf.mapPayload_comp {Middle : Type v} {Target : Type w}
    (f : Payload → Middle) (g : Middle → Target) (image : ImageOf Payload) :
    (image.mapPayload f).mapPayload g = image.mapPayload (g ∘ f) := by
  simp [ImageOf.mapPayload, Array.map_map, Option.map_map,
    Function.comp_def, EntryOf.mapPayload_comp]

theorem ImageOf.mapPayload_roundtrip {Target : Type v}
    (encode : Payload → Target) (decode : Target → Payload)
    (faithful : ∀ payload, decode (encode payload) = payload) (image : ImageOf Payload) :
    (image.mapPayload encode).mapPayload decode = image := by
  rw [ImageOf.mapPayload_comp]
  have composite : decode ∘ encode = id := funext faithful
  rw [composite, ImageOf.mapPayload_id]

/-! ## Shared-allocation canaries

The allocator has two handles and only two permitted generations per handle.
The selected frame occupies handle one, making a rebase to zero observable.
-/

private def firstAllocation : Allocator × Token :=
  (allocate? (Allocator.empty 2 2) 1).get (by decide)

private def retainedAllocation : Allocator :=
  (retain? firstAllocation.1 firstAllocation.2).get (by decide)

private def oneReleased : Allocator :=
  (release? retainedAllocation firstAllocation.2).get (by decide)

private def allReleased : Allocator :=
  (release? oneReleased firstAllocation.2).get (by decide)

private def secondAllocation : Allocator × Token :=
  (allocate? allReleased 1).get (by decide)

private def exhaustedAllocator : Allocator :=
  (release? secondAllocation.1 secondAllocation.2).get (by decide)

private def originalImage : Image :=
  (Image.publish? firstAllocation.1 (Image.empty 2) firstAllocation.2 sampleFrame sampleEnv).get
    (by decide)

private def capturedImage : Allocator × Image :=
  (originalImage.capture? firstAllocation.1 firstAllocation.2).get (by decide)

private def writtenImage : Image :=
  (capturedImage.2.write? (firstAllocation.2.ref 0) (some (.symbol "branch"))).get (by decide)

theorem canary_first_allocation_live : Live firstAllocation.1 firstAllocation.2 := by decide

theorem canary_live_handle_cannot_be_allocated :
    allocate? firstAllocation.1 1 = none := by decide

theorem canary_another_live_allocation_uses_other_handle :
    (allocate? firstAllocation.1 0).map (fun result => result.2) = some ⟨0, 0⟩ ∧
      firstAllocation.2 = ⟨1, 0⟩ := by decide

theorem canary_retain_counts_both_owners :
    retainedAllocation.cells[1]? = some ⟨0, 2⟩ := by decide

theorem canary_one_release_keeps_identity_live :
    Live oneReleased firstAllocation.2 ∧ allocate? oneReleased 1 = none := by decide

theorem canary_final_release_invalidates_identity :
    ¬ Live allReleased firstAllocation.2 ∧ allReleased.cells[1]? = some ⟨1, 0⟩ := by decide

theorem canary_handle_reuse_changes_incarnation :
    secondAllocation.2 = ⟨1, 1⟩ ∧ Live secondAllocation.1 secondAllocation.2 ∧
      ¬ Live secondAllocation.1 firstAllocation.2 := by decide

theorem canary_stale_retain_rejected :
    retain? secondAllocation.1 firstAllocation.2 = none := by decide

theorem canary_stale_release_rejected :
    release? secondAllocation.1 firstAllocation.2 = none := by decide

theorem canary_exhaustion_retires_handle :
    Retired exhaustedAllocator 1 ∧ allocate? exhaustedAllocator 1 = none := by decide

theorem canary_retired_generation_does_not_wrap :
    exhaustedAllocator.cells[1]? = some ⟨2, 0⟩ ∧
      ¬ Live exhaustedAllocator ⟨1, 0⟩ ∧ ¬ Live exhaustedAllocator ⟨1, 1⟩ := by decide

theorem canary_zero_generation_bound_rejects_allocation :
    allocate? (Allocator.empty 2 0) 1 = none := by decide

theorem canary_capture_retains_shared_token :
    capturedImage.1.cells[1]? = some ⟨0, 2⟩ ∧
      capturedImage.2.lookup (firstAllocation.2.ref 0) = some (some (.symbol "before")) ∧
      capturedImage.2.lookup ⟨0, 0, 0⟩ = none := by decide

/-- Equal identity does not imply equal values in different branch images. -/
theorem canary_same_live_variable_different_branch_values :
    Live capturedImage.1 firstAllocation.2 ∧
      originalImage.lookupOwned capturedImage.1 (firstAllocation.2.ref 0) =
        some (some (.symbol "before")) ∧
      writtenImage.lookupOwned capturedImage.1 (firstAllocation.2.ref 0) =
        some (some (.symbol "branch")) := by decide

/-- Old image contents alone are not an ownership certificate. -/
theorem canary_released_image_requires_authority :
    writtenImage.lookup (firstAllocation.2.ref 0) = some (some (.symbol "branch")) ∧
      writtenImage.lookupOwned allReleased (firstAllocation.2.ref 0) = none := by decide

theorem canary_reused_handle_cannot_validate_old_image :
    writtenImage.lookupOwned secondAllocation.1 (firstAllocation.2.ref 0) = none := by decide

theorem canary_exhaustion_follows_protocol : Trace (Allocator.empty 2 2) exhaustedAllocator := by
  have first : Step (Allocator.empty 2 2) firstAllocation.1 :=
    .allocate (handle := 1) (token := firstAllocation.2) (by decide)
  have retained : Step firstAllocation.1 retainedAllocation :=
    .retain (token := firstAllocation.2) (by decide)
  have releasedOne : Step retainedAllocation oneReleased :=
    .release (token := firstAllocation.2) (by decide)
  have releasedAll : Step oneReleased allReleased :=
    .release (token := firstAllocation.2) (by decide)
  have reused : Step allReleased secondAllocation.1 :=
    .allocate (handle := 1) (token := secondAllocation.2) (by decide)
  have exhausted : Step secondAllocation.1 exhaustedAllocator :=
    .release (token := secondAllocation.2) (by decide)
  exact (((((Trace.refl _).next first).next retained).next releasedOne).next releasedAll).next reused
    |>.next exhausted

theorem canary_exhausted_allocator_wellFormed : exhaustedAllocator.WellFormed :=
  canary_exhaustion_follows_protocol.wellFormed (Allocator.empty_wellFormed 2 2)

/-! ## Context-sensitive payload controls

This fixture interprets a retained raw skeleton using a selected lexical frame
at observation. It demonstrates why eagerly freezing a contextual payload can
lose later branch refinements. It is a semantic example, not a correspondence
claim for a native representation or ownership of referenced frames.
-/

private inductive PayloadKind where
  | materialized | contextual | persistent
  deriving DecidableEq

private structure ContextualPayload where
  skeleton : Atom
  context : Token
  kind : PayloadKind
  deriving DecidableEq

private def contextualPayload : ContextualPayload :=
  ⟨.var "x", firstAllocation.2, .contextual⟩

private def contextualStore : StoreOf ContextualPayload :=
  install (StoreOf.empty 2) ⟨0, by decide⟩ sampleFrame
    (fun slot => if slot.val = 0 then some contextualPayload else none)

private def contextualImage : ImageOf ContextualPayload :=
  (ImageOf.publish? firstAllocation.1 (ImageOf.empty 2) firstAllocation.2 sampleFrame
    (fun slot => if slot.val = 0 then some contextualPayload else none)).get (by decide)

private def contextualCapture : Allocator × ImageOf ContextualPayload :=
  (contextualImage.capture? firstAllocation.1 firstAllocation.2).get (by decide)

private def observeContextual (image : Image) (payload : ContextualPayload) : Option Atom :=
  if payload.kind = .materialized then some payload.skeleton
  else do
    let entry ← image.frameAt payload.context.handle
    if entry.generation = payload.context.generation then
      some (SubstitutionAlgebra.subst (MetavariableFrame.denote (entryEnv entry)) payload.skeleton)
    else none

private def contextualEmptyImage : Image :=
  (Image.publish? firstAllocation.1 (Image.empty 2) firstAllocation.2 []
    (fun slot => slot.elim0)).get (by decide)

private def frozenPayload : ContextualPayload :=
  { contextualPayload with
    skeleton := (observeContextual originalImage contextualPayload).get (by decide)
    kind := .materialized }

/-- Raw syntax, lexical incarnation, and payload kind survive indexed storage. -/
theorem canary_contextual_payload_retained :
    lookup contextualStore ⟨0, 0, 0⟩ = some (some contextualPayload) ∧
      lookup contextualStore ⟨0, 0, 1⟩ = some none ∧
      lookup contextualStore ⟨0, 1, 0⟩ = none := by decide

/-- Capture keeps the complete contextual payload and the checked owner transition. -/
theorem canary_contextual_capture_retains_payload :
    contextualCapture.1.cells[1]? = some ⟨0, 2⟩ ∧
      contextualCapture.2.lookupOwned contextualCapture.1 (firstAllocation.2.ref 0) =
        some (some contextualPayload) := by decide

/-- The same retained skeleton follows later branch refinements at its lexical frame. -/
theorem canary_contextual_payload_observes_branch_refinement :
    observeContextual originalImage contextualPayload = some (.symbol "before") ∧
      observeContextual writtenImage contextualPayload = some (.symbol "branch") := by decide

/-- Observing the payload actually read from a captured slot follows its lexical branch. -/
theorem canary_captured_contextual_payload_observes_refinement :
    (contextualCapture.2.lookupOwned contextualCapture.1 (firstAllocation.2.ref 0)).bind
      (fun value => value.bind (observeContextual originalImage)) = some (.symbol "before") ∧
      (contextualCapture.2.lookupOwned contextualCapture.1 (firstAllocation.2.ref 0)).bind
        (fun value => value.bind (observeContextual writtenImage)) = some (.symbol "branch") := by decide

/-- Persistent contextual ownership changes no lexical interpretation. -/
theorem canary_persistent_contextual_observation_agrees :
    observeContextual originalImage { contextualPayload with kind := .persistent } =
      observeContextual originalImage contextualPayload ∧
      observeContextual writtenImage { contextualPayload with kind := .persistent } =
        observeContextual writtenImage contextualPayload := by decide

/-- An empty lexical inventory is a real context; an unresolved raw variable remains syntax. -/
theorem canary_contextual_empty_inventory_preserves_raw_variable :
    contextualEmptyImage.lookup (firstAllocation.2.ref 0) = none ∧
      observeContextual contextualEmptyImage contextualPayload = some (.var "x") ∧
      observeContextual writtenImage contextualPayload = some (.symbol "branch") := by decide

/-- Eager materialization loses the subsequent refinement, despite identical initial value. -/
theorem canary_context_loss_rejects_eager_materialization :
    observeContextual originalImage frozenPayload = observeContextual originalImage contextualPayload ∧
      observeContextual writtenImage frozenPayload ≠ observeContextual writtenImage contextualPayload := by decide

/-- A payload write in the source leaves the captured contextual value intact. -/
theorem canary_contextual_capture_isolates_later_payload_write :
    (contextualImage.write? (firstAllocation.2.ref 0) (some frozenPayload)).map
      (fun next => next.lookupOwned contextualCapture.1 (firstAllocation.2.ref 0)) =
        some (some (some frozenPayload)) ∧
      contextualCapture.2.lookupOwned contextualCapture.1 (firstAllocation.2.ref 0) =
        some (some contextualPayload) := by decide

/-- Equal raw spelling is insufficient when its lexical incarnation is wrong. -/
theorem canary_contextual_wrong_incarnation_rejected :
    observeContextual writtenImage { contextualPayload with context := ⟨1, 1⟩ } = none ∧
      observeContextual writtenImage contextualPayload = some (.symbol "branch") := by decide

/-- A lossy syntax projection retains reference guards while erasing contextual information. -/
theorem canary_skeleton_projection_preserves_guards_loses_context :
    lookup (contextualStore.mapPayload ContextualPayload.skeleton) ⟨0, 0, 0⟩ =
      some (some (.var "x")) ∧
      lookup (contextualStore.mapPayload ContextualPayload.skeleton) ⟨0, 0, 1⟩ = some none ∧
      lookup (contextualStore.mapPayload ContextualPayload.skeleton) ⟨0, 1, 0⟩ = none ∧
      observeContextual writtenImage { contextualPayload with kind := .materialized } ≠
        observeContextual writtenImage contextualPayload := by
  simp only [lookup_mapPayload]
  decide

/-- The generic store does not reinterpret persistent payload metadata. -/
theorem canary_persistent_payload_kind_retained :
    lookup (install (StoreOf.empty 2) ⟨0, by decide⟩ sampleFrame
      (fun _ => some { contextualPayload with kind := .persistent })) ⟨0, 0, 0⟩ =
        some (some { contextualPayload with kind := .persistent }) := by decide

/-- Rollback restores contextual contents without reviving the discarded allocation. -/
theorem canary_contextual_rollback_preserves_payload :
    let speculative := install contextualStore ⟨0, by decide⟩ sampleFrame
      (fun _ => some frozenPayload)
    let restored := rollback speculative contextualStore
    lookup restored ⟨0, 0, 0⟩ = some (some contextualPayload) ∧
      lookup restored ⟨0, 1, 0⟩ = none ∧ restored.nextGeneration = 2 := by decide

/-! ## Whole-directory contextual ownership controls -/

private def twoFirstAllocation : Allocator × Token :=
  (allocate? (Allocator.empty 3 3) 0).get (by decide)

private def twoSecondAllocation : Allocator × Token :=
  (allocate? twoFirstAllocation.1 1).get (by decide)

private def twoContextualPayload : ContextualPayload :=
  ⟨.var "x", twoSecondAllocation.2, .contextual⟩

private def twoLexicalPayload : ContextualPayload :=
  ⟨.symbol "lexical", twoSecondAllocation.2, .materialized⟩

private def twoFrameImage : ImageOf ContextualPayload :=
  let first := (ImageOf.publish? twoSecondAllocation.1 (ImageOf.empty 3) twoFirstAllocation.2
    sampleFrame (fun slot => if slot.val = 0 then some twoContextualPayload else none)).get (by decide)
  (first.publish? twoSecondAllocation.1 twoSecondAllocation.2 sampleFrame
    (fun slot => if slot.val = 0 then some twoLexicalPayload else none)).get (by decide)

private def twoWholeCapture : Allocator × ImageOf ContextualPayload :=
  (twoFrameImage.captureAll? twoSecondAllocation.1).get (by decide)

private def twoSelectedCapture : Allocator × ImageOf ContextualPayload :=
  (twoFrameImage.capture? twoSecondAllocation.1 twoFirstAllocation.2).get (by decide)

private def twoWholeReleasedFirst : Allocator :=
  (release? twoWholeCapture.1 twoFirstAllocation.2).get (by decide)

private def twoWholeReleasedSecond : Allocator :=
  (release? twoWholeReleasedFirst twoSecondAllocation.2).get (by decide)

private def twoSelectedReleasedFirst : Allocator :=
  (release? twoSelectedCapture.1 twoFirstAllocation.2).get (by decide)

private def twoSelectedReleasedSecond : Allocator :=
  (release? twoSelectedReleasedFirst twoSecondAllocation.2).get (by decide)

private def twoStaleAuthority : Allocator :=
  (release? twoSecondAllocation.1 twoSecondAllocation.2).get (by decide)

private def observeOwnedContextual (allocator : Allocator)
    (image : ImageOf ContextualPayload) (payload : ContextualPayload) : Option Atom :=
  if payload.kind = .materialized then some payload.skeleton
  else do
    let entry ← image.frameAt payload.context.handle
    if Live allocator payload.context ∧ entry.generation = payload.context.generation then
      some (SubstitutionAlgebra.subst (MetavariableFrame.denote
        (MetavariableFrame.mapPayload ContextualPayload.skeleton (entryEnv entry))) payload.skeleton)
    else none

theorem canary_whole_inventory_is_actual_frames :
    twoFrameImage.inventory = [twoFirstAllocation.2, twoSecondAllocation.2] := by decide

theorem canary_whole_capture_counts_every_frame_once :
    twoWholeCapture.1.cells[0]? = some ⟨0, 2⟩ ∧
      twoWholeCapture.1.cells[1]? = some ⟨0, 2⟩ ∧
      twoWholeCapture.1.cells[2]? = some ⟨0, 0⟩ := by decide

/-- The payload lives in frame zero and resolves in frame one after both source owners release. -/
theorem canary_whole_capture_protects_referenced_context :
    twoWholeCapture.2.lookupOwned twoWholeReleasedSecond (twoFirstAllocation.2.ref 0) =
      some (some twoContextualPayload) ∧
      observeOwnedContextual twoWholeReleasedSecond twoWholeCapture.2 twoContextualPayload =
        some (.symbol "lexical") ∧
      twoWholeCapture.2.lookupOwned twoWholeReleasedSecond (twoSecondAllocation.2.ref 1) =
        some none ∧
      twoWholeCapture.2.lookupOwned twoWholeReleasedSecond ⟨2, 0, 0⟩ = none := by decide

/-- Projection alone drops the frame needed to interpret the raw payload. -/
theorem canary_selected_capture_loses_referenced_frame :
    twoSelectedCapture.2.lookupOwned twoSelectedCapture.1 (twoFirstAllocation.2.ref 0) =
      some (some twoContextualPayload) ∧
      observeOwnedContextual twoSelectedCapture.1 twoSelectedCapture.2 twoContextualPayload = none := by decide

/-- Keeping the complete value image without retaining its lexical token still loses authority. -/
theorem canary_selected_capture_loses_referenced_owner :
    Live twoSelectedReleasedSecond twoFirstAllocation.2 ∧
      ¬ Live twoSelectedReleasedSecond twoSecondAllocation.2 ∧
      observeOwnedContextual twoSelectedReleasedSecond twoFrameImage twoContextualPayload = none := by decide

/-- A later stale token fails the whole batch even when the initial retain would succeed. -/
theorem canary_whole_capture_stale_reference_refuses_publication :
    (retain? twoStaleAuthority twoFirstAllocation.2).isSome = true ∧
      (twoFrameImage.capture? twoStaleAuthority twoFirstAllocation.2).isSome = true ∧
      (twoFrameImage.captureAll? twoStaleAuthority).isSome = false := by decide

/-- Empty frame inventories still own their exact allocation incarnation. -/
theorem canary_whole_capture_retains_empty_inventory :
    (contextualEmptyImage.captureAll? firstAllocation.1).map
      (fun captured => captured.1.cells[1]?) = some (some ⟨0, 2⟩) ∧
      (contextualEmptyImage.captureAll? firstAllocation.1).map
        (fun captured => captured.2.lookup (firstAllocation.2.ref 0)) = some none := by decide

/-! ## Directory-clock and unbound-slot capture controls -/

private def lineageWritten : Image :=
  (originalImage.write? (firstAllocation.2.ref 0) (some (.symbol "earlier"))).get (by decide)

private def lineageActivated : Image :=
  (lineageWritten.activate? firstAllocation.2).get (by decide)

private def lineageProjected : Image :=
  lineageActivated.projectSlots (fun _ slot => decide (slot = 1))

private def lineageCapture : Allocator × Image :=
  (lineageProjected.capture? firstAllocation.1 firstAllocation.2).get (by decide)

private def lineageLater : Image :=
  (lineageCapture.2.write? (firstAllocation.2.ref 1) (some (.symbol "later"))).get (by decide)

private def lineageClockReset : Image := { lineageCapture.2 with writeClock := 0 }

private def lineageBadLater : Image :=
  (lineageClockReset.write? (firstAllocation.2.ref 1) (some (.symbol "later"))).get (by decide)

private def lineageCleared : Image :=
  (lineageLater.write? (firstAllocation.2.ref 1) none).get (by decide)

/-- A projection with no assignments still retains the frame and its chronology. -/
theorem canary_unbound_capture_retains_lineage :
    lineageProjected.lookup (firstAllocation.2.ref 0) = some none ∧
      lineageProjected.lookup (firstAllocation.2.ref 1) = some none ∧
      lineageCapture.2.readSlotOwned? lineageCapture.1 (firstAllocation.2.ref 1) =
        some ⟨none, 0, 1, some 1⟩ := by decide

/-- The later write uses a fresh directory-clock reading and is visible to
the retained activation view. -/
theorem canary_unbound_capture_later_write_visible :
    lineageLater.writeClock = 2 ∧
      lineageLater.readSlotOwned? lineageCapture.1 (firstAllocation.2.ref 1) =
        some ⟨some (.symbol "later"), 2, 2, some 1⟩ ∧
      (lineageLater.readSlot? (firstAllocation.2.ref 1)).bind
        (SlotReadbackOf.outputAfter 1) = some (.symbol "later") := by decide

/-- Resetting just the directory clock suffices to hide the later write from
the same activation view, even though value lookup still finds it. -/
theorem canary_reset_clock_loses_activation_write :
    lineageBadLater.lookup (firstAllocation.2.ref 1) = some (some (.symbol "later")) ∧
      (lineageBadLater.readSlot? (firstAllocation.2.ref 1)).bind
        (SlotReadbackOf.outputAfter 1) = none := by decide

/-- Explicit unbinding is still a write. Projection preserves its version,
while out-of-range coordinates remain invalid. -/
theorem canary_unbound_version_is_retained :
    (lineageCleared.projectSlots (fun _ slot => decide (slot = 1))).readSlot?
        (firstAllocation.2.ref 1) = some ⟨none, 3, 3, some 1⟩ ∧
      lineageCleared.readSlot? (firstAllocation.2.ref 2) = none := by decide

theorem canary_lineage_readback_needs_live_authority :
    lineageCapture.2.readSlotOwned? allReleased (firstAllocation.2.ref 1) = none ∧
      lineageCapture.2.readSlotOwned? secondAllocation.1 (firstAllocation.2.ref 1) = none := by decide

/-- Saved versions and boundaries return on rollback; consumed clock readings
are not reused by the next write. -/
theorem canary_rollback_keeps_clock_and_restores_slot_history :
    let saved := install (empty 2) ⟨0, by decide⟩ sampleFrame (fun _ => none)
    let written := (write? saved ⟨0, 0, 1⟩ (some (.symbol "discarded"))).get (by decide)
    let restored := rollback written saved
    restored.writeClock = 1 ∧
      MetavariableFrameStore.readSlot? restored ⟨0, 0, 1⟩ = some ⟨none, 0, 1, none⟩ ∧
      ((write? restored ⟨0, 0, 1⟩ (some (.symbol "new"))).get (by decide)).writeClock = 2 := by decide

end Shared

end Mettapedia.Languages.MeTTa.MetavariableFrameStore

/-! ## Complete current slot observations

The ordered snapshot includes bound and known-open slots, along with their
reference identity and write history. It is exactly characterized by the
existing checked slot reader and makes no assumption about payload meaning.
-/

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore.Snapshot

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MetavariableFrameStore.Shared

universe u

/-- One observed slot retains its identity and complete logical write history.
The authored name is source syntax, not a replacement for the reference. -/
structure RowOf (Payload : Type u) where
  reference : Ref
  name : String
  observed : SlotReadbackOf Payload
  deriving DecidableEq, Repr

abbrev Row := RowOf Atom

variable {Payload : Type u}

def Row.ofEntry (handle : Nat) (entry : EntryOf Payload) (clock : Nat)
    (slot : Fin entry.frame.length) : RowOf Payload :=
  ⟨⟨handle, entry.generation, slot.val⟩, entry.frame[slot.val],
    ⟨entryEnv entry slot,
      entry.writeVersions[slot.val]'(by rw [entry.versions_size_eq]; exact slot.isLt),
      clock, entry.activationBoundary⟩⟩

def entryRows (handle : Nat) (entry : EntryOf Payload) (clock : Nat) : List (RowOf Payload) :=
  List.ofFn (Row.ofEntry handle entry clock)

/-- Enumerate every actual present frame and every slot, including unbound
slots. Frame and slot order are the existing directory and inventory orders. -/
def rows (image : ImageOf Payload) : List (RowOf Payload) :=
  (List.range image.entries.size).flatMap fun handle =>
    match image.frameAt handle with
    | none => []
    | some entry => entryRows handle entry image.writeClock

/-- A named view uses the existing generation-checked raw slot reader. -/
def readRow? (image : ImageOf Payload) (reference : Ref) : Option (RowOf Payload) :=
  match image.frameAt reference.handle with
  | none => none
  | some entry =>
    match entry.frame[reference.slot]? with
    | none => none
    | some name => (image.readSlot? reference).map (fun observed => ⟨reference, name, observed⟩)

theorem image_frameAt (image : ImageOf Payload) (handle : Nat) :
    image.frameAt handle = (image.entries[handle]?).getD none := rfl

theorem frameAt_bound {image : ImageOf Payload} {handle : Nat} {entry : EntryOf Payload}
    (present : image.frameAt handle = some entry) : handle < image.entries.size := by
  change (image.entries[handle]?).getD none = some entry at present
  by_contra outside
  simp [Array.getElem?_eq_none (Nat.not_lt.mp outside)] at present

theorem readRow?_of_entry {image : ImageOf Payload} {handle : Nat} {entry : EntryOf Payload}
    (present : image.frameAt handle = some entry) (slot : Fin entry.frame.length) :
    readRow? image ⟨handle, entry.generation, slot.val⟩ =
      some (Row.ofEntry handle entry image.writeClock slot) := by
  have raw : image.readSlot? ⟨handle, entry.generation, slot.val⟩ =
      entry.readSlot? image.writeClock slot.val := by
    exact readSlot?_of_frameAt present rfl
  simp [readRow?, present, slot.isLt, raw, EntryOf.readSlot?_valid, Row.ofEntry]

theorem mem_rows {image : ImageOf Payload} {row : RowOf Payload} :
    row ∈ rows image ↔ ∃ handle : Nat, ∃ entry : EntryOf Payload, ∃ slot : Fin entry.frame.length,
      image.frameAt handle = some entry ∧
      row = Row.ofEntry handle entry image.writeClock slot := by
  constructor
  · intro member
    obtain ⟨handle, _, entryMember⟩ := List.mem_flatMap.mp member
    cases present : image.frameAt handle with
    | none => simp [present] at entryMember
    | some entry =>
      simp only [present] at entryMember
      obtain ⟨slot, equal⟩ := List.mem_ofFn.mp entryMember
      exact ⟨handle, entry, slot, present, equal.symm⟩
  · rintro ⟨handle, entry, slot, present, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨handle, List.mem_range.mpr (frameAt_bound present), ?_⟩
    simp only [present, entryRows, List.mem_ofFn]
    exact ⟨slot, rfl⟩

theorem rows_readback {image : ImageOf Payload} {row : RowOf Payload} (member : row ∈ rows image) :
    readRow? image row.reference = some row := by
  obtain ⟨handle, entry, slot, present, rfl⟩ := mem_rows.mp member
  exact readRow?_of_entry present slot

theorem readRow?_mem_rows {image : ImageOf Payload} {reference : Ref} {row : RowOf Payload}
    (read : readRow? image reference = some row) : row ∈ rows image := by
  unfold readRow? at read
  cases present : image.frameAt reference.handle with
  | none => simp [present] at read
  | some entry =>
    simp only [present] at read
    cases named : entry.frame[reference.slot]? with
    | none => simp [named] at read
    | some name =>
      have bound : reference.slot < entry.frame.length := List.getElem?_eq_some_iff.mp named |>.1
      have guarded : image.readSlot? reference =
          if entry.generation = reference.generation then
            entry.readSlot? image.writeClock reference.slot else none := by
        change MetavariableFrameStore.readSlot? ⟨image.entries, 0, image.writeClock⟩ reference = _
        have actual : MetavariableFrameStore.frameAt
            ⟨image.entries, 0, image.writeClock⟩ reference.handle = some entry := present
        simp [MetavariableFrameStore.readSlot?, actual]
      by_cases generation : entry.generation = reference.generation
      · have exactRead := readRow?_of_entry present ⟨reference.slot, bound⟩
        have referenceEq : reference = ⟨reference.handle, entry.generation, reference.slot⟩ := by
          cases reference
          simp_all
        have equal : row = Row.ofEntry reference.handle entry image.writeClock
            ⟨reference.slot, bound⟩ := by
          have original : readRow? image reference = some row := by
            simpa only [readRow?, present] using read
          rw [referenceEq] at original
          exact Option.some.inj (exactRead.symm.trans original) |>.symm
        exact mem_rows.mpr ⟨reference.handle, entry, ⟨reference.slot, bound⟩, present, equal⟩
      · simp [named, guarded, generation] at read

theorem rows_complete {image : ImageOf Payload} {row : RowOf Payload} :
    row ∈ rows image ↔ readRow? image row.reference = some row :=
  ⟨rows_readback, readRow?_mem_rows⟩

theorem readRow?_stale {image : ImageOf Payload} {reference : Ref} {entry : EntryOf Payload}
    (present : image.frameAt reference.handle = some entry)
    (stale : entry.generation ≠ reference.generation) : readRow? image reference = none := by
  have raw : image.readSlot? reference = none := MetavariableFrameStore.readSlot?_stale present stale
  cases named : entry.frame[reference.slot]? <;> simp [readRow?, present, named, raw]

theorem rows_reference_unique (image : ImageOf Payload) :
    ((rows image).map RowOf.reference).Nodup := by
  let atHandle (handle : Nat) : List Ref :=
    (match image.frameAt handle with
     | none => []
     | some entry => entryRows handle entry image.writeClock).map RowOf.reference
  have hasHandle : ∀ handle reference, reference ∈ atHandle handle → reference.handle = handle := by
    intro handle reference member
    cases present : image.frameAt handle with
    | none => simp [atHandle, present] at member
    | some entry =>
      simp only [atHandle, present, entryRows, List.map_ofFn, List.mem_ofFn] at member
      obtain ⟨slot, rfl⟩ := member
      rfl
  change ((List.range image.entries.size).flatMap _ |>.map RowOf.reference).Nodup
  rw [List.map_flatMap]
  change ((List.range image.entries.size).flatMap atHandle).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro handle _
    cases present : image.frameAt handle with
    | none => simp [atHandle, present]
    | some entry =>
      simp only [atHandle, present, entryRows, List.map_ofFn]
      apply List.nodup_ofFn.mpr
      intro left right equal
      exact Fin.ext (congrArg Ref.slot equal)
  · apply List.nodup_range.imp
    intro left right different
    apply List.disjoint_left.mpr
    intro reference first second
    exact different ((hasHandle left reference first).symm.trans (hasHandle right reference second))


end Mettapedia.Languages.MeTTa.MetavariableFrameStore.Snapshot

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore.Snapshot

open MetavariableFrameStore.Shared
universe u
variable {Payload : Type u}

/-- The actual global observation clock advances for every row. Only the
written reference changes its value and slot version; identity and activation
metadata remain part of the same logical observation. -/
def RowOf.afterWrite (clock : Nat) (target : Ref) (value : Option Payload)
    (row : RowOf Payload) : RowOf Payload :=
  { row with observed :=
    { row.observed with
      value := if row.reference = target then value else row.observed.value
      writeVersion := if row.reference = target then clock else row.observed.writeVersion
      writeClock := clock } }

@[simp] theorem RowOf.afterWrite_reference (clock : Nat) (target : Ref) (value : Option Payload)
    (row : RowOf Payload) : (row.afterWrite clock target value).reference = row.reference := rfl

@[simp] theorem RowOf.afterWrite_name (clock : Nat) (target : Ref) (value : Option Payload)
    (row : RowOf Payload) : (row.afterWrite clock target value).name = row.name := rfl

private theorem entryRows_afterWrite (handle : Nat) (entry : EntryOf Payload)
    (oldClock clock slot : Nat) (value : Option Payload) :
    entryRows handle (updateEntry entry slot value clock) clock =
      (entryRows handle entry oldClock).map
        (RowOf.afterWrite clock ⟨handle, entry.generation, slot⟩ value) := by
  simp only [entryRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  have valueBound : index.val < entry.values.size := by
    simpa only [entry.size_eq, updateEntry] using index.isLt
  have versionBound : index.val < entry.writeVersions.size := by
    simpa only [entry.versions_size_eq, updateEntry] using index.isLt
  simp [Row.ofEntry, RowOf.afterWrite, updateEntry, entryEnv, Ref.mk.injEq,
    Function.comp_def, Array.getElem_setIfInBounds valueBound,
    Array.getElem_setIfInBounds versionBound, eq_comm]

private theorem entryRows_otherWrite (handle : Nat) (entry : EntryOf Payload)
    (oldClock clock : Nat) (target : Ref) (value : Option Payload)
    (different : handle ≠ target.handle) :
    entryRows handle entry clock =
      (entryRows handle entry oldClock).map (RowOf.afterWrite clock target value) := by
  simp only [entryRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  have distinct : (⟨handle, entry.generation, index.val⟩ : Ref) ≠ target := by
    intro same
    exact different (congrArg Ref.handle same)
  simp [Row.ofEntry, RowOf.afterWrite, distinct]

/-- Exact ordered snapshot transport for the real checked write operation. -/
theorem rows_write {image next : ImageOf Payload} {target : Ref} {value : Option Payload}
    (written : image.write? target value = some next) :
    rows next = (rows image).map (RowOf.afterWrite next.writeClock target value) := by
  cases result : MetavariableFrameStore.write? (Shared.ImageOf.toStore image) target value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    obtain ⟨entry, present, generation, _bound, rfl⟩ := write?_success result
    simp only [rows, replace, Array.size_setIfInBounds, List.map_flatMap, Shared.ImageOf.toStore]
    apply List.flatMap_congr
    intro handle _
    by_cases same : handle = target.handle
    · subst handle
      have changed := frameAt_replace_self (Shared.ImageOf.toStore image) target.handle
        (Snapshot.frameAt_bound (image := image) present)
        (updateEntry entry target.slot value (image.writeClock + 1))
      change (match frameAt (replace (Shared.ImageOf.toStore image) target.handle
          (updateEntry entry target.slot value (image.writeClock + 1))) target.handle with
        | none => []
        | some actual => entryRows target.handle actual (image.writeClock + 1)) = _
      rw [changed]
      change _ = (match image.frameAt target.handle with
        | none => []
        | some actual => entryRows target.handle actual image.writeClock).map _
      rw [show image.frameAt target.handle = some entry from present]
      have refEq : (⟨target.handle, entry.generation, target.slot⟩ : Ref) = target := by
        cases target
        simp_all
      rw [← refEq]
      exact entryRows_afterWrite _ _ _ _ _ _
    · have unchanged := frameAt_replace_other (Shared.ImageOf.toStore image) target.handle handle (Ne.symm same)
      change (match frameAt (replace (Shared.ImageOf.toStore image) target.handle
          (updateEntry entry target.slot value (image.writeClock + 1))) handle with
        | none => []
        | some actual => entryRows handle actual (image.writeClock + 1)) = _
      rw [unchanged]
      change (match image.frameAt handle with
        | none => []
        | some actual => entryRows handle actual (image.writeClock + 1)) = _
      cases observed : image.frameAt handle with
      | none => rfl
      | some actual => exact entryRows_otherWrite _ _ _ _ _ _ same

/-- Writes retain the exact lexical inventories, allocation generations and
activation boundaries at every directory entry, including empty frames. -/
theorem frameInfo_write {image next : ImageOf Payload} {target : Ref} {value : Option Payload}
    (written : image.write? target value = some next) (handle : Nat) :
    (next.frameAt handle).map (fun entry => (entry.generation, entry.frame, entry.activationBoundary)) =
      (image.frameAt handle).map (fun entry => (entry.generation, entry.frame, entry.activationBoundary)) := by
  cases result : MetavariableFrameStore.write? (Shared.ImageOf.toStore image) target value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    obtain ⟨entry, present, generation, _bound, rfl⟩ := write?_success result
    by_cases same : handle = target.handle
    · subst handle
      have changed := frameAt_replace_self (Shared.ImageOf.toStore image) target.handle
        (Snapshot.frameAt_bound (image := image) present)
        (updateEntry entry target.slot value (image.writeClock + 1))
      change (frameAt (replace (Shared.ImageOf.toStore image) target.handle
        (updateEntry entry target.slot value (image.writeClock + 1))) target.handle).map _ = _
      rw [changed]
      change _ = (frameAt (Shared.ImageOf.toStore image) target.handle).map _
      rw [present]
      rfl
    · change (frameAt (replace (Shared.ImageOf.toStore image) target.handle
        (updateEntry entry target.slot value (image.writeClock + 1))) handle).map _ = _
      rw [frameAt_replace_other _ _ _ (Ne.symm same)]
      rfl

/-- A successful write neither allocates nor removes directory positions. -/
theorem directorySize_write {image next : ImageOf Payload} {target : Ref} {value : Option Payload}
    (written : image.write? target value = some next) : next.entries.size = image.entries.size := by
  cases result : MetavariableFrameStore.write? (Shared.ImageOf.toStore image) target value with
  | none => simp [ImageOf.write?, result] at written
  | some store =>
    simp only [ImageOf.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    obtain ⟨entry, _present, _generation, _bound, rfl⟩ := write?_success result
    simp [replace, Shared.ImageOf.toStore]

/-- The same ordered generational inventory remains captured by the caller. -/
theorem inventory_write {image next : ImageOf Payload} {target : Ref} {value : Option Payload}
    (written : image.write? target value = some next) : next.inventory = image.inventory := by
  simp only [ImageOf.inventory, directorySize_write written]
  apply List.filterMap_congr
  intro handle _
  have info := frameInfo_write written handle
  have mapped := congrArg (Option.map (fun item : Nat × MetavariableFrame.Frame × Option Nat =>
    (⟨handle, item.1⟩ : Token))) info
  simpa only [Option.map_map, Function.comp_def] using mapped

end Mettapedia.Languages.MeTTa.MetavariableFrameStore.Snapshot
