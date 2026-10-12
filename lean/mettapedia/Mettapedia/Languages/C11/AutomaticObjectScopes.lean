import Mettapedia.Languages.C11.IntegerObjectConstruction

/-!
# Automatic integer object lifetimes and lexical scope frames

Declaration entry constructs owned scalar/array storage before deriving its
identifier binding. Each frame retains the allocation lifetimes it owns.
Leaving a frame retires every retained lifetime and restores the enclosing
bindings. Catalogs and pointer descriptors retain the retired identities, so
an escaped location cannot acquire the identity of a later declaration.

Executable retirement uses the existing finite-storage liveness transition;
its independent rule requires complete ownership and describes the heap kill.
This reuse does not authorize the C library `free` on automatic objects.
Source timing of non-VLA block entry, source initializer execution, VLA
evaluation, abrupt exits and native stack/allocator refinement are separate
parts of the source-machine connection. The entry and exit operations here
make those lifetime endpoints available for a constructed source adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.AutomaticObjectScopes

open IntegerObjectConstruction ByteRanges ByteStorageData ObjectAccessMemory
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

variable {Byte : Type}

/-- A lifetime endpoint needs its live header and every owned byte. -/
def Retirement (before : Heap (Excl (Option Byte))) (identity : BlockId)
    (after : Heap (Excl (Option Byte))) : Prop :=
  ∃ extent, HoldsBlock before identity extent ∧ after = before.kill identity extent

def retireStorage (storage : Storage.State Byte) (identity : BlockId) : Option (Storage.State Byte) :=
  ExecutableStorage.free storage (some ⟨identity, 0⟩)

theorem retireStorage_sound (storage saved : Storage.State Byte) (identity : BlockId)
    (executed : retireStorage storage identity = some saved) :
    Retirement (ByteRanges.heap storage) identity (ByteRanges.heap saved) := by
  obtain ⟨safe, stepped⟩ := ExecutableStorage.free_sound storage saved (some ⟨identity, 0⟩) executed
  obtain ⟨_, extent, holds⟩ := safe
  obtain ⟨otherExtent, header, final⟩ := stepped
  have equal : otherExtent = extent := by
    have headers := Excl.own.inj (header.symm.trans holds.1)
    exact congrArg Header.size headers
  subst otherExtent
  exact ⟨extent, holds, final⟩

theorem retireStorage_complete (storage : Storage.State Byte) (identity : BlockId)
    (after : Heap (Excl (Option Byte)))
    (retired : Retirement (ByteRanges.heap storage) identity after) :
    ∃ saved, retireStorage storage identity = some saved ∧ ByteRanges.heap saved = after := by
  obtain ⟨extent, holds, final⟩ := retired
  exact ExecutableStorage.free_complete storage (some ⟨identity, 0⟩) after
    ⟨rfl, extent, holds⟩ ⟨extent, holds.1, final⟩

theorem Retirement.frame (before after frame : Heap (Excl (Option Byte))) (identity : BlockId)
    (retired : Retirement before identity after) (separate : before ## frame) :
    Retirement (before + frame) identity (after + frame) ∧ after ## frame := by
  obtain ⟨extent, holds, rfl⟩ := retired
  obtain ⟨commutes, separated⟩ := kill_frame holds separate
  exact ⟨⟨extent, holds.frame separate, commutes.symm⟩, separated⟩

def Dead (memory : Heap (Excl (Option Byte))) (identity : BlockId) : Prop :=
  ∃ extent, (memory identity).1 = .own ⟨extent, false⟩

theorem Retirement.dead (before after : Heap (Excl (Option Byte))) (identity : BlockId)
    (retired : Retirement before identity after) : Dead after identity := by
  obtain ⟨extent, _, rfl⟩ := retired
  exact ⟨extent, by simp only [Heap.kill, Function.update_self, Heap.killedBlock]⟩

theorem Retirement.other (before after : Heap (Excl (Option Byte))) (identity other : BlockId)
    (retired : Retirement before identity after) (different : other ≠ identity) : after other = before other := by
  obtain ⟨_, _, rfl⟩ := retired
  exact Function.update_of_ne different _ _

theorem Dead.not_live (memory : Heap (Excl (Option Byte))) (identity : BlockId)
    (dead : Dead memory identity) (extent : Nat) : (memory identity).1 ≠ .own ⟨extent, true⟩ := by
  obtain ⟨_, header⟩ := dead
  rw [header]
  simp

theorem dead_range_unreadable (memory : Heap (Excl (Option Byte))) (range : Range)
    (dead : Dead memory range.address.allocation) (contents : List (Option Byte)) :
    ¬ ReadRange memory range contents := by
  rintro ⟨extent, header, _⟩
  exact dead.not_live _ _ extent header

theorem dead_readBytes_refused (storage : Storage.State Byte) (range : Range)
    (dead : Dead (ByteRanges.heap storage) range.address.allocation) : readBytes storage range = none := by
  cases computed : readBytes storage range with
  | none => rfl
  | some contents => exact False.elim (dead_range_unreadable _ _ dead contents (readBytes_sound _ _ _ computed))

theorem dead_integer_read_refused (layout : ObjectAccessMemory.Layout)
    (memory : ObjectAccessMemory.State layout.representation.characters) (location : Lvalue)
    (dead : Dead (ByteRanges.heap memory.storage) location.object.address.allocation) :
    ObjectAccessMemory.read layout memory location = none := by
  cases computed : ObjectAccessMemory.read layout memory location with
  | none => rfl
  | some outcome =>
      obtain ⟨_, _, _, _, _, bytes, reading, _⟩ := ObjectAccessMemory.read_sound _ _ _ _ computed
      exact False.elim (dead_range_unreadable _
        ⟨location.object.address, layout.representation.byteCount⟩ dead _ reading)

theorem dead_array_unresolvable (storage : Storage.State Byte) (arrays : ArrayPointers.Catalog)
    (identity : BlockId) (descriptor : ArrayPointers.Descriptor)
    (namesLifetime : descriptor.allocation = identity)
    (dead : Dead (ByteRanges.heap storage) identity) (object : Nat) :
    ¬ ArrayPointers.LiveArray (ByteRanges.heap storage) arrays object descriptor := by
  rintro ⟨_, _, extent, header, _⟩
  rw [namesLifetime] at header
  exact dead.not_live _ _ extent header

inductive Release : Heap (Excl (Option Byte)) → List BlockId → Heap (Excl (Option Byte)) → Prop where
  | empty (memory : Heap (Excl (Option Byte))) : Release memory [] memory
  | cons (before middle after : Heap (Excl (Option Byte))) (identity : BlockId) (rest : List BlockId)
      (retired : Retirement before identity middle) (following : Release middle rest after) :
      Release before (identity :: rest) after

def releaseStorage (storage : Storage.State Byte) : List BlockId → Option (Storage.State Byte)
  | [] => some storage
  | identity :: rest => do
      let saved ← retireStorage storage identity
      releaseStorage saved rest

theorem releaseStorage_sound (storage saved : Storage.State Byte) (identities : List BlockId)
    (executed : releaseStorage storage identities = some saved) :
    Release (ByteRanges.heap storage) identities (ByteRanges.heap saved) := by
  induction identities generalizing storage with
  | nil => simp only [releaseStorage, Option.some.injEq] at executed; subst saved; exact .empty _
  | cons identity rest ih =>
      simp only [releaseStorage, bind, Option.bind_eq_some_iff] at executed
      obtain ⟨middle, retired, following⟩ := executed
      exact .cons _ _ _ _ _ (retireStorage_sound _ _ _ retired) (ih middle following)

theorem releaseStorage_complete (storage : Storage.State Byte) (identities : List BlockId)
    (after : Heap (Excl (Option Byte))) (released : Release (ByteRanges.heap storage) identities after) :
    ∃ saved, releaseStorage storage identities = some saved ∧ ByteRanges.heap saved = after := by
  generalize present : ByteRanges.heap storage = before at released
  induction released generalizing storage with
  | empty memory => exact ⟨storage, rfl, present⟩
  | cons before middle after identity rest retired following ih =>
      rw [← present] at retired
      obtain ⟨step, stepped, middleEqual⟩ := retireStorage_complete storage identity middle retired
      obtain ⟨saved, remainder, afterEqual⟩ := ih step middleEqual
      exact ⟨saved, by simp only [releaseStorage, stepped, bind, Option.bind_some, remainder], afterEqual⟩

theorem Release.frame (before after frame : Heap (Excl (Option Byte))) (identities : List BlockId)
    (released : Release before identities after) (separate : before ## frame) :
    Release (before + frame) identities (after + frame) ∧ after ## frame := by
  induction released with
  | empty memory => exact ⟨.empty _, separate⟩
  | cons before middle after identity rest retired following ih =>
      obtain ⟨retiredFrame, middleSeparate⟩ := retired.frame _ _ _ _ separate
      obtain ⟨followingFrame, finalSeparate⟩ := ih middleSeparate
      exact ⟨.cons _ _ _ _ _ retiredFrame followingFrame, finalSeparate⟩

theorem Release.other (before after : Heap (Excl (Option Byte))) (identities : List BlockId)
    (released : Release before identities after) (other : BlockId) (outside : other ∉ identities) :
    after other = before other := by
  induction released with
  | empty => rfl
  | cons before middle after identity rest retired following ih =>
      have different : other ≠ identity := fun same => outside (List.mem_cons.mpr (.inl same))
      have followingOutside : other ∉ rest := fun member => outside (List.mem_cons_of_mem _ member)
      exact (ih followingOutside).trans (retired.other _ _ _ _ different)

theorem Retirement.preserves_dead (before after : Heap (Excl (Option Byte))) (identity other : BlockId)
    (retired : Retirement before identity after) (dead : Dead before other) : Dead after other := by
  by_cases same : other = identity
  · subst other; exact retired.dead _ _ _
  · obtain ⟨extent, header⟩ := dead
    exact ⟨extent, by rw [retired.other _ _ _ _ same]; exact header⟩

theorem Release.preserves_dead (before after : Heap (Excl (Option Byte))) (identities : List BlockId)
    (released : Release before identities after) (other : BlockId) (dead : Dead before other) : Dead after other := by
  induction released with
  | empty => exact dead
  | cons before middle after identity rest retired following ih =>
      exact ih (retired.preserves_dead _ _ _ _ dead)

theorem Release.all_dead (before after : Heap (Excl (Option Byte))) (identities : List BlockId)
    (released : Release before identities after) (other : BlockId) (member : other ∈ identities) : Dead after other := by
  induction released with
  | empty => cases member
  | cons before middle after identity rest retired following ih =>
      rcases List.mem_cons.mp member with same | followingMember
      · subst other; exact following.preserves_dead _ _ _ _ (retired.dead _ _ _)
      · exact ih followingMember

/-- Consecutive lifetime releases compose in their actual order. -/
theorem Release.append {before middle after : Heap (Excl (Option Byte))}
    {first second : List BlockId} (earlier : Release before first middle)
    (suffix : Release middle second after) : Release before (first ++ second) after := by
  induction earlier with
  | empty => exact suffix
  | cons before next middle identity rest retired following ih =>
    exact .cons _ _ _ _ _ retired (ih suffix)

theorem Release.exists (before : Heap (Excl (Option Byte))) (identities : List BlockId)
    (unique : identities.Nodup) (owned : ∀ identity ∈ identities, ∃ extent, HoldsBlock before identity extent) :
    ∃ after, Release before identities after := by
  induction identities generalizing before with
  | nil => exact ⟨before, .empty _⟩
  | cons identity rest ih =>
      obtain ⟨notFollowing, uniqueFollowing⟩ := List.nodup_cons.mp unique
      obtain ⟨extent, holds⟩ := owned identity (List.mem_cons_self)
      have retired : Retirement before identity (before.kill identity extent) := ⟨extent, holds, rfl⟩
      have remaining : ∀ other ∈ rest, ∃ size, HoldsBlock (before.kill identity extent) other size := by
        intro other member
        have different : other ≠ identity := fun same => notFollowing (same ▸ member)
        obtain ⟨size, held⟩ := owned other (List.mem_cons_of_mem _ member)
        refine ⟨size, ?_⟩
        simpa only [HoldsBlock, Heap.kill, Function.update_of_ne different] using held
      obtain ⟨after, following⟩ := ih _ uniqueFollowing remaining
      exact ⟨after, .cons _ _ _ _ _ retired following⟩

structure Frame where
  bindings : ScopedLvalues.Frame := []
  allocations : List BlockId := []
  deriving DecidableEq, Repr

structure State (model : IntegerMemoryModel.Model) where
  memory : ObjectAccessMemory.State model.characters
  arrays : ArrayPointers.Catalog
  frames : List Frame
  deriving DecidableEq, Repr

structure SemanticState (model : IntegerMemoryModel.Model) where
  memory : ObjectAccessMemory.SemanticState model.characters
  arrays : ArrayPointers.Catalog
  frames : List Frame

def represent (model : IntegerMemoryModel.Model) (state : State model) : SemanticState model :=
  ⟨ObjectAccessMemory.represent state.memory, state.arrays, state.frames⟩

def environment {model : IntegerMemoryModel.Model} (state : State model) : ScopedLvalues.Environment :=
  state.frames.map Frame.bindings

def enter {model : IntegerMemoryModel.Model} (state : State model) : State model :=
  { state with frames := {} :: state.frames }

def declare (model : IntegerMemoryModel.Model) (state : State model) (declaration : Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents) : Option (State model) := do
  match state.frames with
  | [] => none
  | frame :: rest =>
      if frame.bindings.lookup declaration.name = none then
        let object ← construct model state.memory state.arrays declaration element identity mode
        some ⟨object.memory, object.arrays,
          ⟨(declaration.name, object.location) :: frame.bindings, identity :: frame.allocations⟩ :: rest⟩
      else none

def DeclarationEntry (model : IntegerMemoryModel.Model) (before : SemanticState model) (declaration : Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents) (after : SemanticState model) : Prop :=
  ∃ frame rest, before.frames = frame :: rest ∧ ScopedLvalues.FrameAbsent declaration.name frame.bindings ∧
    Creation model before.memory before.arrays declaration element identity mode after.memory after.arrays
      (root declaration element identity) ∧
    after.frames = ⟨(declaration.name, root declaration element identity) :: frame.bindings,
      identity :: frame.allocations⟩ :: rest

theorem declare_sound (model : IntegerMemoryModel.Model) (state saved : State model) (declaration : Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (executed : declare model state declaration element identity mode = some saved) :
    DeclarationEntry model (represent model state) declaration element identity mode (represent model saved) := by
  cases scopes : state.frames with
  | nil => simp only [declare, scopes] at executed; cases executed
  | cons frame rest =>
      by_cases absent : frame.bindings.lookup declaration.name = none
      · simp only [declare, scopes, if_pos absent, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
        obtain ⟨object, created, rfl⟩ := executed
        have creation := construct_sound _ _ _ _ _ _ _ _ created
        have location := creation.2.2.2.2.2.2
        refine ⟨frame, rest, scopes, (ScopedLvalues.lookup_absent_iff _ _).mp absent, ?_, ?_⟩
        · simpa only [represent, location] using creation
        · simp only [represent, location]
      · simp only [declare, scopes, if_neg absent] at executed; cases executed

theorem declare_complete (model : IntegerMemoryModel.Model) (state : State model) (declaration : Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents) (after : SemanticState model)
    (entry : DeclarationEntry model (represent model state) declaration element identity mode after) :
    ∃ saved, declare model state declaration element identity mode = some saved ∧ represent model saved = after := by
  obtain ⟨frame, rest, scopes, absent, creation, frames⟩ := entry
  obtain ⟨object, created, memory, arrays, location⟩ := construct_complete _ _ _ _ _ _ _ _ _ _ creation
  change construct model state.memory state.arrays declaration element identity mode = some object at created
  refine ⟨⟨object.memory, object.arrays,
    ⟨(declaration.name, object.location) :: frame.bindings, identity :: frame.allocations⟩ :: rest⟩, ?_, ?_⟩
  · have missing := (ScopedLvalues.lookup_absent_iff _ _).mpr absent
    change state.frames = frame :: rest at scopes
    simp only [declare, scopes, if_pos missing, created, bind, Option.bind_some]
  · cases after
    simp_all only [represent]

def leave (model : IntegerMemoryModel.Model) (state : State model) : Option (State model) := do
  match state.frames with
  | [] => none
  | frame :: rest =>
      let storage ← releaseStorage state.memory.storage frame.allocations
      some ⟨⟨storage, state.memory.catalog⟩, state.arrays, rest⟩

def ScopeExit (model : IntegerMemoryModel.Model) (before after : SemanticState model) : Prop :=
  ∃ frame rest, before.frames = frame :: rest ∧ after.frames = rest ∧
    Release before.memory.memory frame.allocations after.memory.memory ∧
    after.memory.catalog = before.memory.catalog ∧ after.arrays = before.arrays

theorem leave_sound (model : IntegerMemoryModel.Model) (state saved : State model)
    (executed : leave model state = some saved) : ScopeExit model (represent model state) (represent model saved) := by
  cases scopes : state.frames with
  | nil => simp only [leave, scopes] at executed; cases executed
  | cons frame rest =>
      simp only [leave, scopes, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
      obtain ⟨storage, released, rfl⟩ := executed
      exact ⟨frame, rest, scopes, rfl, releaseStorage_sound _ _ _ released, rfl, rfl⟩

theorem leave_complete (model : IntegerMemoryModel.Model) (state : State model) (after : SemanticState model)
    (exit : ScopeExit model (represent model state) after) :
    ∃ saved, leave model state = some saved ∧ represent model saved = after := by
  obtain ⟨frame, rest, scopes, frames, release, catalog, arrays⟩ := exit
  obtain ⟨storage, released, memory⟩ := releaseStorage_complete _ _ _ release
  refine ⟨⟨⟨storage, state.memory.catalog⟩, state.arrays, rest⟩, ?_, ?_⟩
  · change state.frames = frame :: rest at scopes
    simp only [leave, scopes, released, bind, Option.bind_some]
  · cases after with
    | mk semanticMemory semanticArrays semanticFrames =>
      cases semanticMemory
      simp_all only [represent, ObjectAccessMemory.represent]

theorem declaration_resolves (model : IntegerMemoryModel.Model) (state saved : State model)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (executed : declare model state declaration element identity mode = some saved) :
    ScopedLvalues.Binding declaration.name (environment saved) (root declaration element identity) := by
  obtain ⟨frame, rest, _, _, _, frames⟩ := declare_sound _ _ _ _ _ _ _ executed
  change saved.frames = _ at frames
  rw [environment, frames]
  exact .here _ _ _ (.here _ _)

theorem scope_exit_restores_environment (model : IntegerMemoryModel.Model) (state saved : State model)
    (executed : leave model state = some saved) (frame : Frame) (rest : List Frame)
    (scopes : state.frames = frame :: rest) : environment saved = rest.map Frame.bindings := by
  obtain ⟨other, remaining, before, after, _, _, _⟩ := leave_sound _ _ _ executed
  change state.frames = other :: remaining at before
  change saved.frames = remaining at after
  have same := List.cons.inj (before.symm.trans scopes)
  exact congrArg (List.map Frame.bindings) (after.trans same.2)

theorem scope_exit_invalidates (model : IntegerMemoryModel.Model) (state saved : State model)
    (executed : leave model state = some saved) (frame : Frame) (rest : List Frame)
    (scopes : state.frames = frame :: rest) (identity : BlockId) (member : identity ∈ frame.allocations) :
    Dead (ByteRanges.heap saved.memory.storage) identity := by
  obtain ⟨other, remaining, before, _, release, _, _⟩ := leave_sound _ _ _ executed
  change state.frames = other :: remaining at before
  have same := List.cons.inj (before.symm.trans scopes)
  rw [same.1] at release
  exact release.all_dead _ _ _ _ member

theorem scope_exit_preserves_other_block (model : IntegerMemoryModel.Model) (state saved : State model)
    (executed : leave model state = some saved) (frame : Frame) (rest : List Frame)
    (scopes : state.frames = frame :: rest) (identity : BlockId) (outside : identity ∉ frame.allocations) :
    ByteRanges.heap saved.memory.storage identity = ByteRanges.heap state.memory.storage identity := by
  obtain ⟨other, remaining, before, _, release, _, _⟩ := leave_sound _ _ _ executed
  change state.frames = other :: remaining at before
  have same := List.cons.inj (before.symm.trans scopes)
  rw [same.1] at release
  exact release.other _ _ _ _ outside

theorem declaration_without_scope_refused (model : IntegerMemoryModel.Model) (state : State model)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (empty : state.frames = []) : declare model state declaration element identity mode = none := by
  simp only [declare, empty]

theorem redeclaration_refused (model : IntegerMemoryModel.Model) (state : State model)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (frame : Frame) (rest : List Frame) (scopes : state.frames = frame :: rest)
    (location : Lvalue) (occupied : ScopedLvalues.FrameBinding declaration.name frame.bindings location) :
    declare model state declaration element identity mode = none := by
  have found := (ScopedLvalues.lookup_frame_iff _ _ _).mpr occupied
  have notAbsent : frame.bindings.lookup declaration.name ≠ none := by rw [found]; simp
  simp only [declare, scopes, if_neg notAbsent]

def allocations {model : IntegerMemoryModel.Model} (state : State model) : List BlockId :=
  state.frames.flatMap Frame.allocations

def WellScoped {model : IntegerMemoryModel.Model} (state : State model) : Prop :=
  (allocations state).Nodup ∧ ∀ identity ∈ allocations state,
    ∃ extent, HoldsBlock (ByteRanges.heap state.memory.storage) identity extent

theorem enter_wellScoped (model : IntegerMemoryModel.Model) (state : State model) (valid : WellScoped state) :
    WellScoped (enter state) := by
  simpa only [WellScoped, allocations, enter, List.flatMap_cons, List.nil_append, List.flatMap_nil] using valid

theorem declare_wellScoped (model : IntegerMemoryModel.Model) (state saved : State model)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (valid : WellScoped state) (executed : declare model state declaration element identity mode = some saved) :
    WellScoped saved := by
  obtain ⟨frame, rest, scopes, _, creation, frames⟩ := declare_sound _ _ _ _ _ _ _ executed
  have block := creation.2.2.2.1
  have fresh := block.1
  have notOwned : identity ∉ allocations state := by
    intro member
    obtain ⟨extent, held⟩ := valid.2 identity member
    change ByteRanges.heap state.memory.storage identity = 0 at fresh
    have header := held.1
    rw [fresh] at header
    simp only [Prod.fst_zero, Excl.zero_def, reduceCtorEq] at header
  have newAllocations : allocations saved = identity :: allocations state := by
    change state.frames = frame :: rest at scopes
    change saved.frames = _ at frames
    simp only [allocations, frames, scopes, List.flatMap_cons, List.cons_append]
  constructor
  · rw [newAllocations]
    exact List.nodup_cons.mpr ⟨notOwned, valid.1⟩
  · intro other member
    rw [newAllocations] at member
    rcases List.mem_cons.mp member with same | old
    · subst other
      exact ⟨_, block.holds _ _ _ _⟩
    · have different : other ≠ identity := fun same => notOwned (same ▸ old)
      obtain ⟨extent, held⟩ := valid.2 other old
      refine ⟨extent, ?_⟩
      have unchanged : ByteRanges.heap saved.memory.storage other = ByteRanges.heap state.memory.storage other :=
        block.2.2.2 other different
      simpa only [HoldsBlock, unchanged] using held

theorem leave_exists (model : IntegerMemoryModel.Model) (state : State model)
    (valid : WellScoped state) (frame : Frame) (rest : List Frame) (scopes : state.frames = frame :: rest) :
    ∃ saved, leave model state = some saved := by
  have unique := valid.1
  simp only [allocations, scopes, List.flatMap_cons] at unique
  have owned : ∀ identity ∈ frame.allocations, ∃ extent, HoldsBlock (ByteRanges.heap state.memory.storage) identity extent := by
    intro identity member
    apply valid.2 identity
    simp only [allocations, scopes, List.flatMap_cons, List.mem_append]
    exact .inl member
  obtain ⟨after, release⟩ := Release.exists _ _ (List.nodup_append.mp unique).1 owned
  obtain ⟨storage, released, _⟩ := releaseStorage_complete state.memory.storage frame.allocations after release
  exact ⟨⟨⟨storage, state.memory.catalog⟩, state.arrays, rest⟩,
    by simp only [leave, scopes, released, bind, Option.bind_some]⟩

theorem leave_wellScoped (model : IntegerMemoryModel.Model) (state saved : State model)
    (valid : WellScoped state) (executed : leave model state = some saved) : WellScoped saved := by
  obtain ⟨frame, rest, scopes, frames, release, _, _⟩ := leave_sound _ _ _ executed
  change state.frames = frame :: rest at scopes
  change saved.frames = rest at frames
  have unique := valid.1
  simp only [allocations, scopes, List.flatMap_cons] at unique
  obtain ⟨_, outerUnique, disjoint⟩ := List.nodup_append.mp unique
  refine ⟨?_, ?_⟩
  · simpa only [allocations, frames] using outerUnique
  · intro identity member
    change identity ∈ saved.frames.flatMap Frame.allocations at member
    rw [frames] at member
    have outside : identity ∉ frame.allocations := by
      intro inner
      exact disjoint identity inner identity member rfl
    have old : identity ∈ allocations state := by
      simp only [allocations, scopes, List.flatMap_cons, List.mem_append]
      exact .inr member
    obtain ⟨extent, held⟩ := valid.2 identity old
    have unchanged : ByteRanges.heap saved.memory.storage identity = ByteRanges.heap state.memory.storage identity :=
      release.other _ _ _ identity outside
    refine ⟨extent, ?_⟩
    simpa only [HoldsBlock, unchanged] using held

/-! ## Unwinding nested automatic scopes -/

/-- Retire exactly the requested innermost frames. An invalid lifetime or a
request beyond the frame boundary refuses instead of retiring an outer frame. -/
def unwind (model : IntegerMemoryModel.Model) : Nat → State model → Option (State model)
  | 0, state => some state
  | count + 1, state => do
    let saved ← leave model state
    unwind model count saved

/-- Independent scope-exit derivations specify the same ordered unwind. -/
inductive Unwind (model : IntegerMemoryModel.Model) :
    Nat → SemanticState model → SemanticState model → Prop where
  | zero (state) : Unwind model 0 state state
  | step (count before middle after) : ScopeExit model before middle →
      Unwind model count middle after → Unwind model (count + 1) before after

theorem unwind_sound (model : IntegerMemoryModel.Model) (count : Nat) (state saved : State model)
    (executed : unwind model count state = some saved) :
    Unwind model count (represent model state) (represent model saved) := by
  induction count generalizing state with
  | zero => simp only [unwind, Option.some.injEq] at executed; subst saved; exact .zero _
  | succ count ih =>
    simp only [unwind, bind, Option.bind_eq_some_iff] at executed
    obtain ⟨middle, exited, following⟩ := executed
    exact .step _ _ _ _ (leave_sound _ _ _ exited) (ih middle following)

theorem unwind_complete (model : IntegerMemoryModel.Model) (count : Nat) (state : State model)
    (after : SemanticState model) (exited : Unwind model count (represent model state) after) :
    ∃ saved, unwind model count state = some saved ∧ represent model saved = after := by
  generalize represented : represent model state = before at exited
  induction exited generalizing state with
  | zero before => exact ⟨state, rfl, represented⟩
  | step count before middle after exit following ih =>
    rw [← represented] at exit
    obtain ⟨next, exited, representedNext⟩ := leave_complete model state middle exit
    obtain ⟨saved, unwound, representedSaved⟩ := ih next representedNext
    exact ⟨saved, by simp only [unwind, exited, bind, Option.bind_some, unwound], representedSaved⟩

/-- A finite cleanup can be split into two actual residual operations. -/
theorem unwind_add (model : IntegerMemoryModel.Model) (first second : Nat) (state : State model) :
    unwind model (first + second) state =
      (unwind model first state).bind (unwind model second) := by
  induction first generalizing state with
  | zero => simp [unwind]
  | succ first ih =>
    simp only [Nat.succ_add, unwind, bind]
    cases leave model state <;> simp [ih]

theorem Unwind.frames {model : IntegerMemoryModel.Model} {count : Nat}
    {before after : SemanticState model} (unwound : Unwind model count before after) :
    after.frames = before.frames.drop count := by
  induction unwound with
  | zero => rfl
  | step count before middle after exit following ih =>
    obtain ⟨frame, rest, beforeFrames, middleFrames, _, _, _⟩ := exit
    simpa only [beforeFrames, middleFrames, List.drop_succ_cons] using ih

theorem Unwind.frame_count {model : IntegerMemoryModel.Model} {count : Nat}
    {before after : SemanticState model} (unwound : Unwind model count before after) :
    after.frames.length + count = before.frames.length := by
  induction unwound with
  | zero => omega
  | step count before middle after exit following ih =>
    obtain ⟨frame, rest, beforeFrames, middleFrames, _, _, _⟩ := exit
    simp only [beforeFrames, middleFrames, List.length_cons] at *
    omega

/-- The heap ends exactly the lifetimes belonging to the removed frames. -/
theorem Unwind.release {model : IntegerMemoryModel.Model} {count : Nat}
    {before after : SemanticState model} (unwound : Unwind model count before after) :
    Release before.memory.memory ((before.frames.take count).flatMap Frame.allocations) after.memory.memory := by
  induction unwound with
  | zero => exact .empty _
  | step count before middle after exit following ih =>
    obtain ⟨frame, rest, beforeFrames, middleFrames, retired, _, _⟩ := exit
    rw [middleFrames] at ih
    simpa only [beforeFrames, List.take_succ_cons, List.flatMap_cons] using retired.append ih

theorem Unwind.catalogs {model : IntegerMemoryModel.Model} {count : Nat}
    {before after : SemanticState model} (unwound : Unwind model count before after) :
    after.memory.catalog = before.memory.catalog ∧ after.arrays = before.arrays := by
  induction unwound with
  | zero => exact ⟨rfl, rfl⟩
  | step count before middle after exit following ih =>
    obtain ⟨_, _, _, _, _, catalog, arrays⟩ := exit
    exact ⟨ih.1.trans catalog, ih.2.trans arrays⟩

theorem unwind_restores_environment (model : IntegerMemoryModel.Model) (count : Nat)
    (state saved : State model) (executed : unwind model count state = some saved) :
    environment saved = (state.frames.drop count).map Frame.bindings :=
  congrArg (List.map Frame.bindings) (unwind_sound model count state saved executed).frames

theorem unwind_invalidates_owned_lifetime (model : IntegerMemoryModel.Model) (count : Nat)
    (state saved : State model) (executed : unwind model count state = some saved)
    (identity : BlockId) (owned : identity ∈ (state.frames.take count).flatMap Frame.allocations) :
    Dead (ByteRanges.heap saved.memory.storage) identity :=
  (unwind_sound model count state saved executed).release.all_dead _ _ _ _ owned

/-- This protects prior writes to every object outside the cleanup footprint;
unwinding is lifetime retirement, not restoration of an old memory snapshot. -/
theorem unwind_preserves_other_block (model : IntegerMemoryModel.Model) (count : Nat)
    (state saved : State model) (executed : unwind model count state = some saved)
    (identity : BlockId) (outside : identity ∉ (state.frames.take count).flatMap Frame.allocations) :
    ByteRanges.heap saved.memory.storage identity = ByteRanges.heap state.memory.storage identity :=
  (unwind_sound model count state saved executed).release.other _ _ _ _ outside

theorem unwind_wellScoped (model : IntegerMemoryModel.Model) (count : Nat) (state saved : State model)
    (valid : WellScoped state) (executed : unwind model count state = some saved) : WellScoped saved := by
  induction count generalizing state with
  | zero => simp only [unwind, Option.some.injEq] at executed; subst saved; exact valid
  | succ count ih =>
    simp only [unwind, bind, Option.bind_eq_some_iff] at executed
    obtain ⟨middle, exited, following⟩ := executed
    exact ih middle (leave_wellScoped _ _ _ valid exited) following

theorem unwind_exists (model : IntegerMemoryModel.Model) (count : Nat) (state : State model)
    (valid : WellScoped state) (bounded : count ≤ state.frames.length) :
    ∃ saved, unwind model count state = some saved := by
  induction count generalizing state with
  | zero => exact ⟨state, rfl⟩
  | succ count ih =>
    cases scopes : state.frames with
    | nil => simp [scopes] at bounded
    | cons frame rest =>
      obtain ⟨middle, exited⟩ := leave_exists model state valid frame rest scopes
      obtain ⟨other, tail, before, after, _, _, _⟩ := leave_sound model state middle exited
      change state.frames = other :: tail at before
      change middle.frames = tail at after
      have same := List.cons.inj (before.symm.trans scopes)
      have smaller : count ≤ middle.frames.length := by
        simp only [scopes, List.length_cons] at bounded
        rw [after, same.2]
        omega
      obtain ⟨saved, following⟩ := ih middle (leave_wellScoped _ _ _ valid exited) smaller
      exact ⟨saved, by simp only [unwind, exited, bind, Option.bind_some, following]⟩

/-- Complete frame ownership makes the scope boundary the only possible
refusal: no independently valid lifetime is silently abandoned. -/
theorem unwind_exists_iff (model : IntegerMemoryModel.Model) (count : Nat) (state : State model)
    (valid : WellScoped state) :
    (∃ saved, unwind model count state = some saved) ↔ count ≤ state.frames.length := by
  constructor
  · rintro ⟨saved, executed⟩
    have counted := (unwind_sound model count state saved executed).frame_count
    change saved.frames.length + count = state.frames.length at counted
    omega
  · exact unwind_exists model count state valid

theorem unwind_over_boundary_refused (model : IntegerMemoryModel.Model) (count : Nat) (state : State model)
    (crossed : state.frames.length < count) : unwind model count state = none := by
  cases executed : unwind model count state with
  | none => rfl
  | some saved =>
    have counted := (unwind_sound model count state saved executed).frame_count
    change saved.frames.length + count = state.frames.length at counted
    omega

end Mettapedia.Languages.C11.AutomaticObjectScopes
