import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.FinRange
import Mettapedia.Languages.MeTTa.MetavariableFrameStoreEscape

/-!
# Write clocks and activation boundaries of a frame lineage

A frame lineage carries more than its slot values. A monotone directory write
clock stamps writes, and each frame's activation boundary records the clock
reading at which its activation began. Activation output consists of slots
written after that boundary. A frame view retains both independently of slot
boundness; the actual directory owns the clock.

* `project` keeps a subset of the slots and always keeps the clock and the
  boundary. Observation commutes with it (`project_output`), continuing in the
  projection agrees with continuing in the full image and then projecting
  (`project_writes`), and merging any continuation of the projection back into
  its ancestor is exact (`mergeBack_project_writes`).
* `gatedProject` keeps the clock and boundary only when some kept slot is bound.
  After one write through such an image, merging back classifies that write as
  preceding the activation and gives two writes one version
  (`gated_merge_loses_output`, `gated_merge_reuses_version`).
* Logical emptiness, the absence of bound slots, is not absence of lineage
  (`logically_empty_keeps_lineage`).

`Frame.ofEntry` reads this invariant from the existing generational frame store.
Its clock is sampled from the directory, and valid unbound slots are represented
with their separate versions. Actual store writes commute with the adapter;
capture and owned escape retain its observations. The carrier and rollback laws
live in `MetavariableFrameStore`; C memory, layout and imperative correspondence
remain separate obligations. Exact image transfer preserves versions; a general
logical merge may re-stamp them in its recipient's chronology.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameLineage

universe u v

/-- One frame of a lineage: its write clock, its activation boundary, and each
slot's value together with the version of the write that produced it. -/
@[ext]
structure Frame (V : Type u) (n : Nat) where
  clock : Nat
  boundary : Option Nat
  slots : Fin n → Option (V × Nat)

namespace Frame

variable {V : Type u} {n : Nat}

/-- A write advances the clock and stamps the slot with the new reading. -/
def write (f : Frame V n) (i : Fin n) (v : V) : Frame V n where
  clock := f.clock + 1
  boundary := f.boundary
  slots := Function.update f.slots i (some (v, f.clock + 1))

/-- Transport payloads without changing the sampled clock or any version. -/
def mapPayload {W : Type v} (encode : V → W) (f : Frame V n) : Frame W n where
  clock := f.clock
  boundary := f.boundary
  slots := fun i => (f.slots i).map (fun pair => (encode pair.1, pair.2))

/-- A sequence of writes, oldest first. -/
def writes (f : Frame V n) : List (Fin n × V) → Frame V n
  | [] => f
  | (i, v) :: rest => (f.write i v).writes rest

/-- Begin an activation at the current clock reading. -/
def activate (f : Frame V n) : Frame V n := { f with boundary := some f.clock }

/-- A version belongs to the current activation when it follows the boundary.
Without a boundary every version does. -/
def after (f : Frame V n) (version : Nat) : Bool := f.boundary.all (· < version)

/-- The activation output at a slot. -/
def output (f : Frame V n) (i : Fin n) : Option V :=
  match f.slots i with
  | some (v, version) => if f.after version then some v else none
  | none => none

/-- No slot is bound. -/
def LogicallyEmpty (f : Frame V n) : Prop := ∀ i, f.slots i = none

/-- Keep the selected slots, and the lineage's clock and boundary. -/
def project (keep : Fin n → Bool) (f : Frame V n) : Frame V n where
  clock := f.clock
  boundary := f.boundary
  slots := fun i => if keep i then f.slots i else none

/-- Return a continuation's image to its ancestor: the continuation's slots
take precedence, the clock is the later reading, and the activation boundary is
the ancestor's own. -/
def mergeBack (ancestor child : Frame V n) : Frame V n where
  clock := max ancestor.clock child.clock
  boundary := ancestor.boundary
  slots := fun i => (child.slots i).or (ancestor.slots i)

/-- A projection which carries the clock and the boundary only together with a
bound kept slot. -/
def gatedProject (keep : Fin n → Bool) (f : Frame V n) : Frame V n :=
  if (List.finRange n).any (fun i => keep i && (f.slots i).isSome) then f.project keep
  else { clock := 0, boundary := none, slots := (f.project keep).slots }

/-! ## Lineage-preserving projection -/

/-- Observing a projected image is observing the full image at the kept slots. -/
theorem project_output (keep : Fin n → Bool) (f : Frame V n) (i : Fin n) :
    (f.project keep).output i = if keep i then f.output i else none := by
  cases h : keep i
  · simp only [output, project, h, if_false, Bool.false_eq_true]
  · simp only [output, project, after, h, if_true]
    rfl

/-- A write to a kept slot commutes with projection. -/
theorem project_write {keep : Fin n → Bool} {i : Fin n} (kept : keep i = true)
    (f : Frame V n) (v : V) :
    (f.project keep).write i v = (f.write i v).project keep := by
  ext1
  · rfl
  · rfl
  · funext j
    by_cases same : j = i
    · subst j
      simp [write, project, kept]
    · simp [write, project, Function.update_of_ne same]

/-- Continuing in the projection agrees with continuing in the full image and
projecting afterwards, for writes to kept slots. -/
theorem project_writes {keep : Fin n → Bool} :
    ∀ (writes : List (Fin n × V)) (f : Frame V n),
      (∀ w ∈ writes, keep w.1 = true) →
      (f.project keep).writes writes = (f.writes writes).project keep
  | [], _, _ => rfl
  | (i, v) :: rest, f, kept => by
      have here : keep i = true := kept (i, v) (List.mem_cons_self ..)
      have later : ∀ w ∈ rest, keep w.1 = true :=
        fun w member => kept w (List.mem_cons_of_mem _ member)
      simp only [writes]
      rw [project_write here f v]
      exact project_writes rest (f.write i v) later

/-- Writes keep the boundary, never move the clock back, never unbind a slot,
and leave unwritten slots unchanged. -/
theorem writes_boundary :
    ∀ (writes : List (Fin n × V)) (f : Frame V n), (f.writes writes).boundary = f.boundary
  | [], _ => rfl
  | (i, v) :: rest, f => by
      simp only [writes]
      rw [writes_boundary rest (f.write i v)]
      rfl

theorem writes_clock_le :
    ∀ (writes : List (Fin n × V)) (f : Frame V n), f.clock ≤ (f.writes writes).clock
  | [], _ => le_refl _
  | (i, v) :: rest, f => by
      simp only [writes]
      exact le_trans (Nat.le_succ f.clock) (writes_clock_le rest (f.write i v))

theorem writes_unbound :
    ∀ (writes : List (Fin n × V)) (f : Frame V n) (j : Fin n),
      (f.writes writes).slots j = none → f.slots j = none
  | [], _, _, absent => absent
  | (i, v) :: rest, f, j, absent => by
      simp only [writes] at absent
      have earlier := writes_unbound rest (f.write i v) j absent
      by_cases same : j = i
      · subst j
        simp [write] at earlier
      · simpa [write, Function.update_of_ne same] using earlier

theorem writes_untouched :
    ∀ (writes : List (Fin n × V)) (f : Frame V n) (j : Fin n),
      (∀ w ∈ writes, w.1 ≠ j) → (f.writes writes).slots j = f.slots j
  | [], _, _, _ => rfl
  | (i, v) :: rest, f, j, untouched => by
      have here : i ≠ j := untouched (i, v) (List.mem_cons_self ..)
      simp only [writes]
      rw [writes_untouched rest (f.write i v) j
        (fun w member => untouched w (List.mem_cons_of_mem _ member))]
      simp [write, Function.update_of_ne (Ne.symm here)]

/-- **Merging back a continuation of a lineage-preserving projection is exact.**
Whatever writes the continuation makes to its kept slots, returning its image to
the ancestor gives the image the ancestor would have reached by making the same
writes itself: the same clock, boundary, values and versions. -/
theorem mergeBack_project_writes {keep : Fin n → Bool} (f : Frame V n)
    (writes : List (Fin n × V)) (kept : ∀ w ∈ writes, keep w.1 = true) :
    f.mergeBack ((f.project keep).writes writes) = f.writes writes := by
  rw [project_writes writes f kept]
  ext1
  · exact Nat.max_eq_right (writes_clock_le writes f)
  · exact (writes_boundary writes f).symm
  · funext j
    simp only [mergeBack, project]
    cases keepJ : keep j
    · have untouched : ∀ w ∈ writes, w.1 ≠ j := by
        intro w member same
        rw [← same, kept w member] at keepJ
        cases keepJ
      simp [writes_untouched writes f j untouched]
    · cases written : (f.writes writes).slots j with
      | some value => simp
      | none => simp [writes_unbound writes f j written]

/-- Activation output after merging back agrees with the ancestor's own run. -/
theorem output_mergeBack_project_writes {keep : Fin n → Bool} (f : Frame V n)
    (writes : List (Fin n × V)) (kept : ∀ w ∈ writes, keep w.1 = true) (i : Fin n) :
    (f.mergeBack ((f.project keep).writes writes)).output i = (f.writes writes).output i := by
  rw [mergeBack_project_writes f writes kept]

/-! ## Controls -/

/-- A frame that wrote its first slot and then began an activation. -/
def ancestor : Frame Nat 2 := ((⟨0, none, fun _ => none⟩ : Frame Nat 2).write 0 11).activate

/-- Keep only the second slot, which is unbound in `ancestor`. -/
def keepSecond : Fin 2 → Bool := fun i => decide (i = 1)

/-- The lineage-preserving projection keeps the clock and boundary although
every kept slot is unbound; the gated projection drops them. -/
theorem gated_drops_lineage :
    (ancestor.project keepSecond).clock = 1 ∧
      (ancestor.project keepSecond).boundary = some 1 ∧
      (ancestor.gatedProject keepSecond).clock = 0 ∧
      (ancestor.gatedProject keepSecond).boundary = none := by
  decide

/-- Logical emptiness is not absence of lineage. -/
theorem logically_empty_keeps_lineage :
    (ancestor.project keepSecond).LogicallyEmpty ∧
      (ancestor.project keepSecond).boundary = some 1 := by
  refine ⟨?_, by decide⟩
  show ∀ i, _ = none
  decide

/-- After one later write through the gated image, merging back classifies that
write as preceding the activation, so the activation output loses it. The
lineage-preserving projection and the ancestor's own write both report it. -/
theorem gated_merge_loses_output :
    (ancestor.mergeBack ((ancestor.gatedProject keepSecond).write 1 22)).output 1 = none ∧
      (ancestor.mergeBack ((ancestor.project keepSecond).write 1 22)).output 1 = some 22 ∧
      (ancestor.write 1 22).output 1 = some 22 := by
  decide

/-- The same merge gives the earlier write and the later write one version. -/
theorem gated_merge_reuses_version :
    ((ancestor.mergeBack ((ancestor.gatedProject keepSecond).write 1 22)).slots 0).map Prod.snd =
        some 1 ∧
      ((ancestor.mergeBack ((ancestor.gatedProject keepSecond).write 1 22)).slots 1).map Prod.snd =
        some 1 ∧
      ((ancestor.mergeBack ((ancestor.project keepSecond).write 1 22)).slots 1).map Prod.snd =
        some 2 := by
  decide

/-- When a kept slot is bound, the gated projection is the lineage-preserving
one, so the two differ exactly when every kept slot is unbound. -/
theorem gated_agrees_with_a_bound_kept_slot :
    ancestor.gatedProject (fun _ => true) = ancestor.project (fun _ => true) := by
  unfold gatedProject
  rw [if_pos (by decide)]

/-! ## The actual generational entry boundary -/

open MetavariableFrameStore
open private updateEntry write?_success frameAt_bound frameAt_replace_self
  from Mettapedia.Languages.MeTTa.MetavariableFrameStore

/-- Every valid inventory slot carries its value option and version, including
unbound slots. The clock comes from the containing directory, not the entry. -/
def ofEntry {Payload : Type u} (clock : Nat) (entry : EntryOf Payload) :
    Frame (Option Payload) entry.frame.length where
  clock := clock
  boundary := entry.activationBoundary
  slots := fun slot => some (entryEnv entry slot,
    entry.writeVersions[slot.val]'(by rw [entry.versions_size_eq]; exact slot.isLt))

/-- The adapter retains raw valid-unbound observations rather than erasing them. -/
theorem ofEntry_readSlot {Payload : Type u} (clock : Nat) (entry : EntryOf Payload)
    (slot : MetavariableFrame.Slot entry.frame) :
    (entry.readSlot? clock slot.val).map (fun row => (row.value, row.writeVersion)) =
      (ofEntry clock entry).slots slot := by
  rw [EntryOf.readSlot?_valid]
  rfl

/-- Activation value observation is the flattened lineage output. Raw readback
remains richer: it distinguishes invalid references from valid unbound slots. -/
theorem ofEntry_output {Payload : Type u} (clock : Nat) (entry : EntryOf Payload)
    (slot : MetavariableFrame.Slot entry.frame) :
    ((ofEntry clock entry).output slot).join =
      (entry.readSlot? clock slot.val).bind SlotReadbackOf.activationOutput := by
  rw [EntryOf.readSlot?_valid]
  simp only [ofEntry, output, after, Option.bind_some]
  unfold SlotReadbackOf.activationOutput
  split <;> simp_all

theorem ofEntry_mapPayload {Payload : Type u} {Target : Type v}
    (encode : Payload → Target) (clock : Nat) (entry : EntryOf Payload) :
    ofEntry clock (entry.mapPayload encode) =
      (ofEntry clock entry).mapPayload (Option.map encode) := by
  ext1
  · rfl
  · rfl
  · funext slot
    simp only [ofEntry, mapPayload, Option.map_some]
    rw [entryEnv_mapPayload]
    rfl

theorem ofEntry_activate {Payload : Type u} (clock : Nat) (entry : EntryOf Payload) :
    ofEntry clock { entry with activationBoundary := some clock } =
      (ofEntry clock entry).activate := rfl

theorem ofEntry_write {Payload : Type u} (clock : Nat) (entry : EntryOf Payload)
    (slot : MetavariableFrame.Slot entry.frame) (value : Option Payload) :
    ofEntry (clock + 1) (updateEntry entry slot.val value (clock + 1)) =
      (ofEntry clock entry).write slot value := by
  ext1
  · rfl
  · rfl
  · funext other
    by_cases same : other = slot
    · subst other
      simp [ofEntry, updateEntry, write, entryEnv]
    · have distinct : other.val ≠ slot.val := fun equality => same (Fin.ext equality)
      change some ((entry.values.setIfInBounds slot.val value)[other.val]'_,
          (entry.writeVersions.setIfInBounds slot.val (clock + 1))[other.val]'_) =
        Function.update (ofEntry clock entry).slots slot (some (value, clock + 1)) other
      erw [Function.update_of_ne same]
      have valuesBound : other.val < entry.values.size := by rw [entry.size_eq]; exact other.isLt
      have versionsBound : other.val < entry.writeVersions.size := by
        rw [entry.versions_size_eq]; exact other.isLt
      erw [Array.getElem_setIfInBounds_ne valuesBound (Ne.symm distinct),
        Array.getElem_setIfInBounds_ne versionsBound (Ne.symm distinct)]
      rfl

/-- This is a homomorphism of a successful existing store operation. Its guard
constructs the entry and valid slot; no source/native correspondence is assumed. -/
theorem store_write_to_lineage {Payload : Type u} {store next : StoreOf Payload}
    {ref : Ref} {value : Option Payload} (written : write? store ref value = some next) :
    ∃ before after, frameAt store ref.handle = some before ∧ frameAt next ref.handle = some after ∧
      after.frame = before.frame ∧ ∃ slot : MetavariableFrame.Slot before.frame,
        slot.val = ref.slot ∧
          HEq (ofEntry next.writeClock after) ((ofEntry store.writeClock before).write slot value) := by
  obtain ⟨entry, present, _, bound, rfl⟩ := write?_success written
  let slot : MetavariableFrame.Slot entry.frame :=
    ⟨ref.slot, by rw [← entry.size_eq]; exact bound⟩
  refine ⟨entry, updateEntry entry ref.slot value (store.writeClock + 1), present,
    frameAt_replace_self store ref.handle (frameAt_bound present) _, rfl, slot, rfl, ?_⟩
  exact heq_of_eq (ofEntry_write store.writeClock entry slot value)

/-- Selected-frame capture retains the actual complete entry and sampled clock. -/
theorem capture_to_lineage {Payload : Type u} {allocator next : Shared.Allocator}
    {image captured : Shared.ImageOf Payload} {token : Shared.Token}
    (success : image.capture? allocator token = some (next, captured)) :
    ∃ entry, image.frameAt token.handle = some entry ∧ captured.frameAt token.handle = some entry ∧
      ofEntry captured.writeClock entry = ofEntry image.writeClock entry := by
  obtain ⟨entry, before, after, _⟩ := Shared.Image.capture_preserves_identity success
  exact ⟨entry, before, after, congrArg (fun clock => ofEntry clock entry)
    (Shared.ImageOf.capture_preserves_clock success)⟩

/-- Slot projection transports the activation-value observer. It does not
identify omitted slots with invalid coordinates: their inventory still exists. -/
theorem project_entry_output {Payload : Type u} (clock : Nat) (entry : EntryOf Payload)
    (keep : Nat → Bool) (slot : MetavariableFrame.Slot entry.frame) :
    ((ofEntry clock (entry.projectSlots keep)).output
      ⟨slot.val, slot.isLt⟩).join =
      if keep slot.val then ((ofEntry clock entry).output slot).join else none := by
  rw [ofEntry_output, EntryOf.readSlot?_projectSlots, ofEntry_output, EntryOf.readSlot?_valid]
  cases keep slot.val <;> simp [SlotReadbackOf.activationOutput]

private def actualFrame : MetavariableFrame.Frame := ["x", "y"]

private def actualStart : StoreOf Nat :=
  install (StoreOf.empty 1) ⟨0, by decide⟩ actualFrame (fun _ => none)

private def actualFirst : StoreOf Nat :=
  (write? actualStart ⟨0, 0, 0⟩ (some 11)).get (by decide)

private def actualActive : StoreOf Nat :=
  (activate? actualFirst 0 0).get (by decide)

private def actualLater : StoreOf Nat :=
  (write? actualActive ⟨0, 0, 1⟩ (some 22)).get (by decide)

private def actualCleared : StoreOf Nat :=
  (write? actualLater ⟨0, 0, 1⟩ none).get (by decide)

private def actualEntry : EntryOf Nat :=
  (frameAt actualCleared 0).get (by decide)

/-- An entry built by actual store operations retains an unbound slot at a
nonzero version. The adapter does not confuse that slot with absence. -/
theorem actual_entry_retains_unbound_version :
    (ofEntry actualCleared.writeClock actualEntry).slots ⟨1, by decide⟩ = some (none, 3) ∧
      (ofEntry actualCleared.writeClock actualEntry).clock = 3 ∧
      (ofEntry actualCleared.writeClock actualEntry).boundary = some 1 ∧
      readSlot? actualCleared ⟨0, 0, 2⟩ = none := by decide

theorem actual_entry_projection_retains_unbound_lineage :
    let projected := actualEntry.projectSlots (fun slot => decide (slot = 1))
    (ofEntry actualCleared.writeClock projected).slots ⟨1, by decide⟩ = some (none, 3) ∧
      (ofEntry actualCleared.writeClock projected).clock = 3 ∧
      (ofEntry actualCleared.writeClock projected).boundary = some 1 := by decide

/-- Value-only observation hides the retained unbound version, while raw
readback still carries it. This is an intentional observer distinction. -/
theorem actual_entry_value_observation_is_coarser :
    ((ofEntry actualCleared.writeClock actualEntry).output ⟨1, by decide⟩).join = none ∧
      readSlot? actualCleared ⟨0, 0, 1⟩ = some ⟨none, 3, 3, some 1⟩ := by decide

theorem actual_store_write_is_lineage_write :
    ∃ before after, frameAt actualActive 0 = some before ∧ frameAt actualLater 0 = some after ∧
      after.frame = before.frame ∧ ∃ slot : MetavariableFrame.Slot before.frame,
        slot.val = 1 ∧
          HEq (ofEntry actualLater.writeClock after)
            ((ofEntry actualActive.writeClock before).write slot (some 22)) :=
  store_write_to_lineage (store := actualActive) (next := actualLater)
    (ref := ⟨0, 0, 1⟩) (value := some 22) (Option.some_get (by decide)).symm

private def actualTwoFrames : StoreOf Nat :=
  let first := install (StoreOf.empty 2) ⟨0, by decide⟩ actualFrame (fun _ => none)
  install first ⟨1, by decide⟩ actualFrame (fun _ => none)

private def actualTwoWrites : StoreOf Nat :=
  let first := (write? actualTwoFrames ⟨0, 0, 0⟩ (some 11)).get (by decide)
  (write? first ⟨1, 1, 0⟩ (some 22)).get (by decide)

/-- Two different frames share one directory clock. Their slot versions retain
the distinct readings at which they were written; no per-frame clock is used. -/
theorem actual_directory_clock_spans_distinct_frames :
    readSlot? actualTwoWrites ⟨0, 0, 0⟩ = some ⟨some 11, 1, 2, none⟩ ∧
      readSlot? actualTwoWrites ⟨1, 1, 0⟩ = some ⟨some 22, 2, 2, none⟩ := by decide

end Frame

end Mettapedia.Languages.MeTTa.MetavariableFrameLineage
