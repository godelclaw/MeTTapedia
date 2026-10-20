import Mettapedia.Machines.OccurrenceMachine
import Mathlib.Data.List.Perm.Basic
import Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

/-!
# Revision-scoped occurrence identities

An evaluator store carries several kinds of identity that must not be
interchanged.  A payload identifies a term value; a logical position identifies
one admitted occurrence of that payload; a store identity and revision delimit
the snapshot in which that position is meaningful.

This module states the small, policy-neutral contract needed at a dispatch/store
boundary.  It does not choose candidate order, matching semantics, or an
evaluation strategy.  An optimized candidate list may permute the exhaustive
list while retaining its occurrence bag, but that is deliberately weaker than
ordered equality.

The definitions are a mathematical contract for a checked native boundary;
they are not by themselves a refinement proof for a particular runtime.
-/

namespace Mettapedia.Machines

/-- A read-only view of one store revision. -/
structure RevisionedStoreView (StoreId Revision Entry : Type) where
  storeId : StoreId
  revision : Revision
  entries : List Entry

/-- A token for one live store revision. -/
structure StoreReadToken (StoreId Revision : Type) where
  storeId : StoreId
  revision : Revision
deriving DecidableEq

/-- Identity of one logical occurrence within one store revision. -/
structure StoreOccurrenceId (StoreId Revision : Type) where
  read : StoreReadToken StoreId Revision
  logicalIndex : Nat
deriving DecidableEq

namespace RevisionedStoreView

variable {StoreId Revision Entry : Type}

theorem getElem?_eq_some_of_mem_zipIdx {entries : List Entry}
    {entry : Entry} {logicalIndex : Nat}
    (member : (entry, logicalIndex) ∈ entries.zipIdx) :
    entries[logicalIndex]? = some entry := by
  have located := List.exists_mem_zipIdx'.mp
    (show ∃ item ∈ entries.zipIdx, item = (entry, logicalIndex) from
      ⟨_, member, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairEquality⟩ := located
  have indexEquality : foundIndex = logicalIndex :=
    (Prod.ext_iff.mp pairEquality).2
  subst indexEquality
  rw [List.getElem?_eq_getElem foundBound]
  exact congrArg some (Prod.ext_iff.mp pairEquality).1

/-- Capture the identity and revision of the current view. -/
def readToken (view : RevisionedStoreView StoreId Revision Entry) :
    StoreReadToken StoreId Revision :=
  ⟨view.storeId, view.revision⟩

/-- Name one logical position in the current view. -/
def occurrenceId (view : RevisionedStoreView StoreId Revision Entry)
    (logicalIndex : Nat) : StoreOccurrenceId StoreId Revision :=
  ⟨view.readToken, logicalIndex⟩

/-- Resolve an occurrence only when both its store and revision agree with the
current view. -/
def resolve [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision) : Option Entry :=
  if id.read.storeId = view.storeId ∧ id.read.revision = view.revision then
    view.entries[id.logicalIndex]?
  else
    none

@[simp] theorem resolve_current [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (logicalIndex : Nat) :
    view.resolve (view.occurrenceId logicalIndex) =
      view.entries[logicalIndex]? := by
  simp [resolve, occurrenceId, readToken]

@[simp] theorem resolve_wrong_store [DecidableEq StoreId]
    [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision)
    (wrongStore : id.read.storeId ≠ view.storeId) :
    view.resolve id = none := by
  simp [resolve, wrongStore]

@[simp] theorem resolve_stale [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision)
    (stale : id.read.revision ≠ view.revision) :
    view.resolve id = none := by
  simp [resolve, stale]

/-- Replace the entries and explicitly advance to a caller-supplied revision.
The contract requires freshness; it does not prescribe a concrete counter. -/
def replaceRevision
    (view : RevisionedStoreView StoreId Revision Entry)
    (nextRevision : Revision) (nextEntries : List Entry) :
    RevisionedStoreView StoreId Revision Entry :=
  ⟨view.storeId, nextRevision, nextEntries⟩

/-- Any genuinely different revision rejects occurrence IDs captured from the
old revision, independently of the new payload list. -/
theorem old_occurrence_rejected_after_revision_change
    [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (nextRevision : Revision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) (logicalIndex : Nat) :
    (view.replaceRevision nextRevision nextEntries).resolve
        (view.occurrenceId logicalIndex) = none := by
  simp [resolve, replaceRevision, occurrenceId, readToken, changed.symm]

/-- Enumerate every logical occurrence in store order.  `zipIdx` ensures that
two equal payloads at different positions retain different identities. -/
def occurrences (view : RevisionedStoreView StoreId Revision Entry) :
    List (StoreOccurrenceId StoreId Revision × Entry) :=
  view.entries.zipIdx.map fun (entry, logicalIndex) =>
    (view.occurrenceId logicalIndex, entry)

@[simp] theorem occurrences_payloads
    (view : RevisionedStoreView StoreId Revision Entry) :
    view.occurrences.map Prod.snd = view.entries := by
  simp [occurrences, Function.comp_def, List.zipIdx_map_fst]

@[simp] theorem occurrences_length
    (view : RevisionedStoreView StoreId Revision Entry) :
    view.occurrences.length = view.entries.length := by
  simp [occurrences]

/-- Every enumerated occurrence resolves to the payload paired with it. -/
theorem resolve_of_mem_occurrences [DecidableEq StoreId]
    [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    {id : StoreOccurrenceId StoreId Revision} {entry : Entry}
    (member : (id, entry) ∈ view.occurrences) :
    view.resolve id = some entry := by
  obtain ⟨⟨found, logicalIndex⟩, zipped, pairEquality⟩ :=
    List.mem_map.mp member
  cases pairEquality
  rw [resolve_current]
  exact getElem?_eq_some_of_mem_zipIdx zipped

/-- Equal payloads do not collapse two distinct logical occurrence IDs. -/
theorem occurrenceId_injective
    (view : RevisionedStoreView StoreId Revision Entry) {left right : Nat}
    (different : left ≠ right) :
    view.occurrenceId left ≠ view.occurrenceId right := by
  intro equalIds
  exact different (congrArg StoreOccurrenceId.logicalIndex equalIds)

/-- Exhaustive candidate equivalence forgets order but retains occurrence
multiplicity and identity. -/
def ExhaustiveCandidateRefinement
    (reference contender :
      List (StoreOccurrenceId StoreId Revision × Entry)) : Prop :=
  contender.Perm reference

/-- Exhaustive refinement transports to the payload bag. -/
theorem ExhaustiveCandidateRefinement.payloads
    {reference contender :
      List (StoreOccurrenceId StoreId Revision × Entry)}
    (refines : ExhaustiveCandidateRefinement reference contender) :
    (contender.map Prod.snd).Perm (reference.map Prod.snd) :=
  refines.map Prod.snd

end RevisionedStoreView

/-! ## Captured child views and owned enumeration

The child carries a captured parent observation and a separate live identity.
Materialization changes its storage mode; writes advance only the child's view.
The cursor captures a view rather than looking up a mutable store at each step.
These are model laws for those native boundaries, not verification of C memory.
-/

namespace OwnedFork

variable {StoreId Entry : Type}

structure Child (StoreId Entry : Type) where
  captured : RevisionedStoreView StoreId Nat Entry
  storeId : StoreId
  revision : Nat
  privateRows : Option (List Entry)

def Child.rows (child : Child StoreId Entry) : List Entry :=
  child.privateRows.getD child.captured.entries

def capture (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId) :
    Child StoreId Entry := ⟨parent, childId, 0, none⟩

def Child.materialize (child : Child StoreId Entry) : Child StoreId Entry :=
  match child.privateRows with
  | none => { child with privateRows := some child.captured.entries }
  | some _ => child

def Child.write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    Child StoreId Entry :=
  let owned := child.materialize
  { owned with privateRows := some (update owned.rows), revision := owned.revision + 1 }

def Child.view (child : Child StoreId Entry) : RevisionedStoreView StoreId Nat Entry :=
  ⟨child.storeId, child.revision, child.rows⟩

@[simp] theorem rows_materialize (child : Child StoreId Entry) :
    child.materialize.rows = child.rows := by
  cases h : child.privateRows <;> simp [Child.materialize, Child.rows, h]

@[simp] theorem captured_materialize (child : Child StoreId Entry) :
    child.materialize.captured = child.captured := by
  cases h : child.privateRows <;> simp [Child.materialize, h]

@[simp] theorem rows_write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    (child.write update).rows = update child.rows := by
  change update child.materialize.rows = update child.rows
  rw [rows_materialize]

@[simp] theorem captured_write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    (child.write update).captured = child.captured := by
  simp [Child.write]

/-- Any finite sequence of local operations agrees with applying those operations
to a private ordered row list, while preserving the complete captured parent. -/
theorem write_sequence (child : Child StoreId Entry)
    (updates : List (List Entry → List Entry)) :
    (updates.foldl Child.write child).rows = updates.foldl (fun rows update => update rows) child.rows ∧
      (updates.foldl Child.write child).captured = child.captured := by
  induction updates generalizing child with
  | nil => exact ⟨rfl, rfl⟩
  | cons update rest ih =>
    simpa [List.foldl_cons] using ih (child.write update)

/-- A child's row list retains repeated occurrences; no set conversion occurs. -/
theorem capture_occurrences (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId) :
    (capture parent childId).view.occurrences.map Prod.snd = parent.entries := by
  simp [capture, Child.view, Child.rows]

/-- Capturing a parent revision gives that revision's entries even if the live
parent later replaces its contents. The old token cannot name the new parent. -/
theorem parent_revision_isolation [DecidableEq StoreId]
    (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId)
    (next : Nat) (rows : List Entry) (changed : next ≠ parent.revision) (index : Nat) :
    (capture parent childId).rows = parent.entries ∧
      (parent.replaceRevision next rows).resolve (parent.occurrenceId index) = none := by
  exact ⟨rfl, parent.old_occurrence_rejected_after_revision_change next rows changed index⟩

structure Cursor (StoreId Entry : Type) where
  captured : RevisionedStoreView StoreId Nat Entry
  next : Nat

def Cursor.step (cursor : Cursor StoreId Entry) : Option (Entry × Cursor StoreId Entry) :=
  cursor.captured.entries[cursor.next]?.map fun row => (row, { cursor with next := cursor.next + 1 })

def Cursor.read (cursor : Cursor StoreId Entry) : Nat → List Entry
  | 0 => []
  | count + 1 => match cursor.step with
    | none => []
    | some (row, rest) => row :: rest.read count

/-- The iterative cursor returns exactly the captured prefix at its current
position, including repeated payloads and an empty prefix at exhaustion. -/
theorem cursor_prefix (cursor : Cursor StoreId Entry) (count : Nat) :
    cursor.read count = (cursor.captured.entries.drop cursor.next).take count := by
  induction count generalizing cursor with
  | zero => simp [Cursor.read]
  | succ count ih =>
    cases h : cursor.captured.entries[cursor.next]? with
    | none =>
      have beyond : cursor.captured.entries.length ≤ cursor.next := by
        exact List.getElem?_eq_none_iff.mp h
      simp [Cursor.read, Cursor.step, h, List.drop_eq_nil_of_le beyond]
    | some row =>
      obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp h
      rw [List.drop_eq_getElem_cons bound]
      simp [Cursor.read, Cursor.step, h, ih, equal]

/-- Reading a pinned cursor after a write does not renew its token's currency.
The cursor returns old rows while the new live child rejects its occurrence ID. -/
theorem cursor_write_separates_read_and_currency [DecidableEq StoreId]
    (child : Child StoreId Entry) (update : List Entry → List Entry) (index count : Nat) :
    (Cursor.mk child.view index).read count = (child.rows.drop index).take count ∧
      (child.write update).view.resolve (child.view.occurrenceId index) = none := by
  constructor
  · exact cursor_prefix _ count
  · cases h : child.privateRows <;>
      simp [Child.write, Child.materialize, Child.view, RevisionedStoreView.resolve,
        RevisionedStoreView.occurrenceId, RevisionedStoreView.readToken, h]

example : (capture (⟨0, 7, [42, 42]⟩ : RevisionedStoreView Nat Nat Nat) 1).rows = [42, 42] := rfl
example : (Cursor.mk (⟨1, 0, [42, 42]⟩ : RevisionedStoreView Nat Nat Nat) 0).read 2 = [42, 42] := rfl

end OwnedFork


/-! ## Checked positional contraction and fresh output publication -/

namespace RevisionedStoreView.Publication

open Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

variable {StoreId Revision Entry : Type}

/-- Removal is by captured position, including distinct equal-valued inputs. -/
def mask (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) : List Bool :=
  view.occurrences.map fun occurrence => decide (occurrence.1.logicalIndex ∉ consumed)

def contracted (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) : Result Entry :=
  compile (mask view consumed) view.entries

/-- Stable old origins are proof observations, not persistent runtime IDs. -/
def retained (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) :
    List (StoreOccurrenceId StoreId Revision × Entry) :=
  view.occurrences.filter fun occurrence => decide (occurrence.1.logicalIndex ∉ consumed)

def updated (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) : RevisionedStoreView StoreId Revision Entry :=
  view.replaceRevision nextRevision ((contracted view consumed).rows ++ outputs)

/-- The source read and every consumed position must be current and distinct.
Even an equal payload replacement must advance the revision. Source currency
does not itself grant execution permission. -/
def publish [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (read : StoreReadToken StoreId Revision)
    (consumed : List Nat) (outputs : List Entry) (nextRevision : Revision) :
    Option (RevisionedStoreView StoreId Revision Entry) :=
  if read = view.readToken ∧ consumed.Nodup ∧
      (∀ index ∈ consumed, index < view.entries.length) ∧ nextRevision ≠ view.revision then
    some (updated view consumed outputs nextRevision)
  else none

/-- New outputs are named in the new revision after the retained prefix. -/
def fresh (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) :
    List (StoreOccurrenceId StoreId Revision × Entry) :=
  outputs.zipIdx.map fun (entry, index) =>
    ((updated view consumed outputs nextRevision).occurrenceId ((contracted view consumed).rows.length + index), entry)

/-- A proof-only origin view; erasing its names gives the actual published rows. -/
def origins (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) :
    List (StoreOccurrenceId StoreId Revision × Entry) :=
  retained view consumed ++ fresh view consumed outputs nextRevision

private theorem contract_predicate {α : Type} (rows : List α) (keep : α → Bool) :
    contract (rows.map keep) rows = rows.filter keep := by
  induction rows with
  | nil => rfl
  | cons row rows ih => cases choice : keep row <;> simp [contract, choice, ih]

theorem retained_erasure (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) :
    (retained view consumed).map Prod.snd = (contracted view consumed).rows := by
  have filtered := contract_predicate view.occurrences
    (fun occurrence => decide (occurrence.1.logicalIndex ∉ consumed))
  unfold retained
  rw [← filtered]
  simp only [mask, contracted, compile_rows_exact, ← contract_map, occurrences_payloads]

theorem origins_erasure (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) :
    (origins view consumed outputs nextRevision).map Prod.snd =
      (updated view consumed outputs nextRevision).entries := by
  simp [origins, fresh, updated, replaceRevision, List.map_map, Function.comp_def,
    retained_erasure, List.zipIdx_map_fst]

theorem retained_order (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) :
    (retained view consumed).Sublist view.occurrences := List.filter_sublist

theorem retained_origin [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (id : StoreOccurrenceId StoreId Revision) (entry : Entry) :
    (id, entry) ∈ retained view consumed ↔
      (id, entry) ∈ view.occurrences ∧ id.logicalIndex ∉ consumed := by
  simp [retained]

theorem contraction_transport (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat) :
    TransportCertificate view.entries.length (contracted view consumed).rows.length
      (contracted view consumed).sourceToTarget := by
  simpa [contracted, mask] using compile_transport_certificate (mask view consumed) view.entries

/-- The new current coordinate has the exact retained old payload. Under a
changed revision, the old name remains origin evidence rather than currency. -/
theorem coordinate_payload [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) (source target : Nat) (entry : Entry)
    (found : view.entries[source]? = some entry)
    (mapped : (contracted view consumed).sourceToTarget[source]? = some (some target)) :
    (updated view consumed outputs nextRevision).resolve
      ((updated view consumed outputs nextRevision).occurrenceId target) = some entry := by
  have same := sourceToTarget_sound (mask view consumed) view.entries source target mapped
  have row : (contracted view consumed).rows[target]? = some entry := same.symm.trans found
  have bound := (List.getElem?_eq_some_iff.mp row).1
  simpa only [resolve_current, updated, replaceRevision, List.getElem?_append_left bound] using row

theorem publication_admitted [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (read : StoreReadToken StoreId Revision)
    (consumed : List Nat) (outputs : List Entry) (nextRevision : Revision)
    (result : RevisionedStoreView StoreId Revision Entry)
    (accepted : publish view read consumed outputs nextRevision = some result) :
    read = view.readToken ∧ consumed.Nodup ∧
      (∀ index ∈ consumed, index < view.entries.length) ∧ nextRevision ≠ view.revision ∧
      result = updated view consumed outputs nextRevision := by
  unfold publish at accepted
  split at accepted
  · rename_i valid
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2, (Option.some.inj accepted).symm⟩
  · contradiction

theorem admitted_inputs_distinct [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (read : StoreReadToken StoreId Revision)
    (consumed : List Nat) (outputs : List Entry) (nextRevision : Revision)
    (result : RevisionedStoreView StoreId Revision Entry)
    (accepted : publish view read consumed outputs nextRevision = some result) :
    (consumed.map view.occurrenceId).Nodup ∧
      ∀ index ∈ consumed, ∃ entry, view.resolve (view.occurrenceId index) = some entry := by
  have valid := publication_admitted view read consumed outputs nextRevision result accepted
  constructor
  · exact valid.2.1.map (fun _ _ equal => congrArg StoreOccurrenceId.logicalIndex equal)
  · intro index member
    have bound := valid.2.2.1 index member
    exact ⟨view.entries[index], by simp [bound]⟩

theorem fresh_output_not_old [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) (changed : nextRevision ≠ view.revision)
    (id : StoreOccurrenceId StoreId Revision) (entry : Entry)
    (created : (id, entry) ∈ fresh view consumed outputs nextRevision) (oldIndex : Nat) :
    id ≠ view.occurrenceId oldIndex := by
  obtain ⟨⟨value, index⟩, _, same⟩ := List.mem_map.mp created
  cases same
  intro equal
  exact changed (congrArg (fun identity => identity.read.revision) equal)

theorem stale_publication_refused [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (read : StoreReadToken StoreId Revision)
    (consumed : List Nat) (outputs : List Entry) (nextRevision : Revision)
    (stale : read ≠ view.readToken) : publish view read consumed outputs nextRevision = none := by
  simp [publish, stale]

theorem old_read_refused_after_replacement [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (replacement : List Entry)
    (changedRevision nextRevision : Revision) (changed : changedRevision ≠ view.revision)
    (consumed : List Nat) (outputs : List Entry) :
    publish (view.replaceRevision changedRevision replacement) view.readToken consumed outputs nextRevision = none := by
  apply stale_publication_refused
  intro same
  exact changed (congrArg StoreReadToken.revision same).symm

theorem same_revision_refused [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (read : StoreReadToken StoreId Revision)
    (consumed : List Nat) (outputs : List Entry) : publish view read consumed outputs view.revision = none := by
  simp [publish]


private theorem occurrence_names_unique (view : RevisionedStoreView StoreId Revision Entry) :
    (view.occurrences.map Prod.fst).Nodup := by
  apply List.Nodup.of_map StoreOccurrenceId.logicalIndex
  simp only [occurrences, occurrenceId, List.map_map, Function.comp_def, List.zipIdx_map_snd]
  exact List.nodup_range'

/-- The whole origin observation is injective, including equal fresh outputs.
Old and new names are disjoint because the revision actually advances. -/
theorem origins_unique [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (consumed : List Nat)
    (outputs : List Entry) (nextRevision : Revision) (changed : nextRevision ≠ view.revision) :
    ((origins view consumed outputs nextRevision).map Prod.fst).Nodup := by
  have oldUnique : ((retained view consumed).map Prod.fst).Nodup :=
    (occurrence_names_unique view).sublist (List.filter_sublist.map Prod.fst)
  have freshUnique : ((fresh view consumed outputs nextRevision).map Prod.fst).Nodup := by
    have unique : (outputs.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range'
    have injective : Function.Injective (fun index =>
        (updated view consumed outputs nextRevision).occurrenceId ((contracted view consumed).rows.length + index)) := by
      intro left right same
      have indices := congrArg StoreOccurrenceId.logicalIndex same
      exact Nat.add_left_cancel indices
    simpa only [fresh, List.map_map, Function.comp_def] using unique.map injective
  simp only [origins, List.map_append]
  apply List.nodup_append.mpr
  refine ⟨oldUnique, freshUnique, ?_⟩
  intro old oldMember new newMember same
  obtain ⟨⟨oldId, oldValue⟩, oldPair, oldName⟩ := List.mem_map.mp oldMember
  obtain ⟨⟨newId, newValue⟩, newPair, newName⟩ := List.mem_map.mp newMember
  have original := (List.mem_filter.mp oldPair).1
  obtain ⟨⟨value, index⟩, _, oldOrigin⟩ := List.mem_map.mp original
  have oldId : oldId = view.occurrenceId index := (congrArg Prod.fst oldOrigin).symm
  have equal : newId = view.occurrenceId index := newName.trans (same.symm.trans (oldName.symm.trans oldId))
  exact fresh_output_not_old view consumed outputs nextRevision changed newId newValue newPair index equal

namespace Controls

private def source : RevisionedStoreView Nat Nat Nat := ⟨1, 7, [42, 42, 99]⟩

/-- Removing one equal input retains the other original; equal outputs get
new distinct names rather than borrowing the removed occurrence's name. -/
theorem equal_inputs_fresh_outputs :
    (publish source source.readToken [0, 2] [42, 42] 8).map (·.entries) = some [42, 42, 42] ∧
      (origins source [0, 2] [42, 42] 8).map Prod.fst =
        [source.occurrenceId 1, (updated source [0, 2] [42, 42] 8).occurrenceId 1,
          (updated source [0, 2] [42, 42] 8).occurrenceId 2] := by decide

/-- Restoring equal data does not restore a captured read. Repeated positions,
out-of-range positions, and a non-advancing publication also refuse. -/
theorem stale_and_invalid_refused :
    publish (source.replaceRevision 8 source.entries) source.readToken [0] [42] 9 = none ∧
      publish source source.readToken [0, 0] [42] 8 = none ∧
      publish source source.readToken [3] [42] 8 = none ∧
      publish source source.readToken [0] [42] 7 = none := by
  simp [publish, source, readToken, replaceRevision]

end Controls

#print axioms retained_erasure
#print axioms origins_erasure
#print axioms contraction_transport
#print axioms coordinate_payload
#print axioms publication_admitted
#print axioms admitted_inputs_distinct
#print axioms fresh_output_not_old
#print axioms old_read_refused_after_replacement
#print axioms same_revision_refused
#print axioms origins_unique
#print axioms Controls.equal_inputs_fresh_outputs
#print axioms Controls.stale_and_invalid_refused

end RevisionedStoreView.Publication


/-! ## Finite publication with persistent proof-only origins -/

namespace RevisionedStoreView.Publication.Finite

open Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

variable {StoreId Entry : Type}

/-- Captured read, consumed positions, outputs and requested next revision. -/
abbrev Request (StoreId Entry : Type) := StoreReadToken StoreId Nat × List Nat × List Entry × Nat

/-- This reference decoration is erased to view. The origin rows are neither
runtime IDs nor a history journal, and do not participate in admission. -/
structure WithOrigins (StoreId Entry : Type) where
  view : RevisionedStoreView StoreId Nat Entry
  rows : List (StoreOccurrenceId StoreId Nat × Entry)

def Lawful (s : WithOrigins StoreId Entry) : Prop :=
  s.rows.map Prod.snd = s.view.entries ∧ (s.rows.map Prod.fst).Nodup ∧
    ∀ origin ∈ s.rows, origin.1.read.storeId = s.view.storeId ∧ origin.1.read.revision ≤ s.view.revision

def initial (view : RevisionedStoreView StoreId Nat Entry) : WithOrigins StoreId Entry :=
  ⟨view, view.occurrences⟩

/-- Strict growth closes the immediate-freshness contract under finite
composition. Reusing an older revision is refused even with current data. -/
def apply [DecidableEq StoreId] (view : RevisionedStoreView StoreId Nat Entry)
    (request : Request StoreId Entry) : Option (RevisionedStoreView StoreId Nat Entry) :=
  if view.revision < request.2.2.2 then
    publish view request.1 request.2.1 request.2.2.1 request.2.2.2
  else none

/-- Contract the existing origin family by current positions, not by each
origin's old logicalIndex. Its old name survives any coordinate shift. -/
def transport (s : WithOrigins StoreId Entry) (request : Request StoreId Entry) :
    List (StoreOccurrenceId StoreId Nat × Entry) :=
  contract (mask s.view request.2.1) s.rows ++
    fresh s.view request.2.1 request.2.2.1 request.2.2.2

def advance [DecidableEq StoreId] (s : WithOrigins StoreId Entry) (request : Request StoreId Entry) :
    Option (WithOrigins StoreId Entry) :=
  (apply s.view request).map fun view => ⟨view, transport s request⟩

def runViews [DecidableEq StoreId] : List (Request StoreId Entry) →
    RevisionedStoreView StoreId Nat Entry → Option (RevisionedStoreView StoreId Nat Entry)
  | [], view => some view
  | request :: rest, view => (apply view request).bind (runViews rest)

def run [DecidableEq StoreId] : List (Request StoreId Entry) → WithOrigins StoreId Entry →
    Option (WithOrigins StoreId Entry)
  | [], s => some s
  | request :: rest, s => (advance s request).bind (run rest)

private theorem contract_sublist {α : Type} (mask : List Bool) (rows : List α) :
    (contract mask rows).Sublist rows := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask ih =>
      cases rows with
      | nil => simp [contract]
      | cons row rows => cases keep <;> simp only [contract]
                         · exact (ih rows).cons row
                         · exact (ih rows).cons_cons row

private theorem fresh_age (view : RevisionedStoreView StoreId Nat Entry)
    (positions : List Nat) (outputs : List Entry) (next : Nat)
    (origin : StoreOccurrenceId StoreId Nat × Entry) (member : origin ∈ fresh view positions outputs next) :
    origin.1.read.storeId = view.storeId ∧ origin.1.read.revision = next := by
  obtain ⟨⟨value, index⟩, _, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨rfl, rfl⟩

theorem initial_lawful (view : RevisionedStoreView StoreId Nat Entry) : Lawful (initial view) := by
  refine ⟨view.occurrences_payloads, occurrence_names_unique view, ?_⟩
  intro origin member
  obtain ⟨⟨value, index⟩, _, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨rfl, Nat.le_refl _⟩

private theorem apply_admitted [DecidableEq StoreId] (view : RevisionedStoreView StoreId Nat Entry)
    (request : Request StoreId Entry) (result : RevisionedStoreView StoreId Nat Entry)
    (accepted : apply view request = some result) :
    view.revision < request.2.2.2 ∧
      publish view request.1 request.2.1 request.2.2.1 request.2.2.2 = some result := by
  unfold apply at accepted
  split at accepted
  · exact ⟨‹_›, accepted⟩
  · contradiction

private theorem transport_erasure (s : WithOrigins StoreId Entry) (request : Request StoreId Entry)
    (lawful : Lawful s) :
    (transport s request).map Prod.snd = (updated s.view request.2.1 request.2.2.1 request.2.2.2).entries := by
  have freshPayloads : (fresh s.view request.2.1 request.2.2.1 request.2.2.2).map Prod.snd = request.2.2.1 := by
    simp [fresh, List.map_map, Function.comp_def, List.zipIdx_map_fst]
  simp only [transport, List.map_append, ← contract_map, lawful.1, freshPayloads,
    updated, replaceRevision, contracted, compile_rows_exact]

/-- All fields of the naming invariant are derived from actual publication,
including injectivity and an upper bound on every surviving origin's age. -/
theorem advance_lawful [DecidableEq StoreId] (s next : WithOrigins StoreId Entry)
    (request : Request StoreId Entry) (lawful : Lawful s) (accepted : advance s request = some next) :
    Lawful next ∧ s.view.revision < next.view.revision ∧ next.view.storeId = s.view.storeId := by
  obtain ⟨view, published, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  have granted := apply_admitted s.view request view published
  have source := publication_admitted s.view request.1 request.2.1 request.2.2.1 request.2.2.2 view granted.2
  have sourceView := source.2.2.2.2
  subst view
  have kept := contract_sublist (mask s.view request.2.1) s.rows
  have oldUnique : ((contract (mask s.view request.2.1) s.rows).map Prod.fst).Nodup :=
    lawful.2.1.sublist (kept.map Prod.fst)
  have combined := origins_unique s.view request.2.1 request.2.2.1 request.2.2.2 (by omega)
  have freshUnique : ((fresh s.view request.2.1 request.2.2.1 request.2.2.2).map Prod.fst).Nodup :=
    (List.nodup_append.mp (by simpa only [origins, List.map_append] using combined)).2.1
  refine ⟨⟨transport_erasure s request lawful, ?_, ?_⟩, granted.1, rfl⟩
  · simp only [transport, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨oldUnique, freshUnique, ?_⟩
    intro old oldMember new newMember equal
    obtain ⟨oldOrigin, oldKept, oldName⟩ := List.mem_map.mp oldMember
    obtain ⟨newOrigin, newCreated, newName⟩ := List.mem_map.mp newMember
    have age := (lawful.2.2 oldOrigin (kept.subset oldKept)).2
    have freshAge := (fresh_age s.view _ _ _ newOrigin newCreated).2
    have sameAge := congrArg (fun id : StoreOccurrenceId StoreId Nat => id.read.revision)
      (oldName.trans (equal.trans newName.symm))
    omega
  · intro origin member
    rcases List.mem_append.mp member with old | created
    · have known := lawful.2.2 origin (kept.subset old)
      exact ⟨known.1, Nat.le_trans known.2 (Nat.le_of_lt granted.1)⟩
    · have known := fresh_age s.view _ _ _ origin created
      exact ⟨known.1, Nat.le_of_eq known.2⟩

/-- Erasing the decoration commutes with every finite actual publication
schedule, including stale or malformed refusal. -/
theorem run_erasure [DecidableEq StoreId] (requests : List (Request StoreId Entry))
    (s : WithOrigins StoreId Entry) : (run requests s).map WithOrigins.view = runViews requests s.view := by
  induction requests generalizing s with
  | nil => rfl
  | cons request rest ih =>
      cases result : apply s.view request with
      | none => simp [run, runViews, advance, result]
      | some view => simpa [run, runViews, advance, result] using ih ⟨view, transport s request⟩

/-- Splitting a fixed publication word retains the whole current origin
family and view. No commutation across changing external permissions is used. -/
theorem run_append [DecidableEq StoreId] (first second : List (Request StoreId Entry))
    (s : WithOrigins StoreId Entry) :
    run (first ++ second) s = (run first s).bind (run second) := by
  induction first generalizing s with
  | nil => rfl
  | cons request rest ih =>
      cases moved : advance s request with
      | none => simp [run, moved]
      | some next => simpa [run, moved] using ih next

theorem run_lawful [DecidableEq StoreId] (requests : List (Request StoreId Entry))
    (s final : WithOrigins StoreId Entry) (lawful : Lawful s) (accepted : run requests s = some final) :
    Lawful final ∧ s.view.revision ≤ final.view.revision ∧ final.view.storeId = s.view.storeId := by
  induction requests generalizing s with
  | nil => cases Option.some.inj accepted; exact ⟨lawful, Nat.le_refl _, rfl⟩
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      have first := advance_lawful s next request lawful moved
      have later := ih next first.1 continued
      exact ⟨later.1, Nat.le_trans (Nat.le_of_lt first.2.1) later.2.1, later.2.2.trans first.2.2⟩

/-- Any later fresh output differs from every earlier origin, whether that
origin is still held or has already been consumed. No spent-history storage
is required: age bounds plus constructed strict revision growth suffice. -/
theorem later_fresh_ne_earlier [DecidableEq StoreId] (requests : List (Request StoreId Entry))
    (s later next : WithOrigins StoreId Entry) (lawful : Lawful s)
    (continued : run requests s = some later) (request : Request StoreId Entry)
    (advanced : advance later request = some next)
    (old : StoreOccurrenceId StoreId Nat × Entry) (earlier : old ∈ s.rows)
    (created : StoreOccurrenceId StoreId Nat × Entry)
    (freshMember : created ∈ fresh later.view request.2.1 request.2.2.1 request.2.2.2) : created.1 ≠ old.1 := by
  have retained := run_lawful requests s later lawful continued
  obtain ⟨view, published, _⟩ := Option.map_eq_some_iff.mp advanced
  have grant := (apply_admitted later.view request view published).1
  have oldAge := (lawful.2.2 old earlier).2
  have newAge := (fresh_age later.view _ _ _ created freshMember).2
  intro same
  have sameAge := congrArg (fun id : StoreOccurrenceId StoreId Nat => id.read.revision) same
  omega

theorem reused_revision_refused [DecidableEq StoreId] (view : RevisionedStoreView StoreId Nat Entry)
    (request : Request StoreId Entry) (old : request.2.2.2 ≤ view.revision) : apply view request = none := by
  simp [apply, Nat.not_lt.mpr old]


theorem mask_indexed {α : Type} (view : RevisionedStoreView StoreId Nat Entry)
    (rows : List α) (positions : List Nat) (lengths : rows.length = view.entries.length) :
    mask view positions = rows.zipIdx.map (fun pair => decide (pair.2 ∉ positions)) := by
  have left : mask view positions = (view.entries.zipIdx.map Prod.snd).map (fun index => decide (index ∉ positions)) := by
    simp only [mask, occurrences, occurrenceId, List.map_map, Function.comp_def]
  have right : rows.zipIdx.map (fun pair => decide (pair.2 ∉ positions)) =
      (rows.zipIdx.map Prod.snd).map (fun index => decide (index ∉ positions)) := by rw [List.map_map]; rfl
  rw [left, right, List.zipIdx_map_snd, List.zipIdx_map_snd, lengths]

theorem contract_indexed {α : Type} (rows : List α) (positions : List Nat) :
    contract (rows.zipIdx.map (fun pair => decide (pair.2 ∉ positions))) rows =
      (rows.zipIdx.filter (fun pair => decide (pair.2 ∉ positions))).map Prod.fst := by
  have filtered := contract_predicate rows.zipIdx (fun pair => decide (pair.2 ∉ positions))
  have mapped := contract_map Prod.fst (rows.zipIdx.map (fun pair => decide (pair.2 ∉ positions))) rows.zipIdx
  rw [List.zipIdx_map_fst] at mapped
  exact mapped.trans (congrArg (List.map Prod.fst) filtered)

private theorem retained_at_iff (s : WithOrigins StoreId Entry) (request : Request StoreId Entry)
    (lawful : Lawful s) (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Entry)
    (found : s.rows[index]? = some origin) :
    origin ∈ contract (mask s.view request.2.1) s.rows ↔ index ∉ request.2.1 := by
  have lengths : s.rows.length = s.view.entries.length := by simpa using congrArg List.length lawful.1
  rw [mask_indexed s.view s.rows request.2.1 lengths, contract_indexed]
  constructor
  · intro kept
    obtain ⟨⟨value, other⟩, filtered, same⟩ := List.mem_map.mp kept
    cases same
    have location := getElem?_eq_some_of_mem_zipIdx (List.mem_filter.mp filtered).1
    obtain ⟨bound, row⟩ := List.getElem?_eq_some_iff.mp found
    obtain ⟨otherBound, otherRow⟩ := List.getElem?_eq_some_iff.mp location
    have unique : s.rows.Nodup := List.Nodup.of_map Prod.fst lawful.2.1
    have sameIndex : other = index := unique.getElem_inj_iff.mp (otherRow.trans row.symm)
    simpa only [sameIndex] using of_decide_eq_true (List.mem_filter.mp filtered).2
  · intro unchosen
    have indexed : (origin, index) ∈ s.rows.zipIdx :=
      List.mem_of_getElem? (i := index) (by simp [found])
    exact List.mem_map.mpr ⟨(origin, index), List.mem_filter.mpr ⟨indexed, by simpa using unchosen⟩, rfl⟩

/-- Later consumption addresses the exact surviving physical name at the
current index. An origin's former logical index is not consulted. -/
theorem advance_name_iff [DecidableEq StoreId] (s next : WithOrigins StoreId Entry)
    (request : Request StoreId Entry) (lawful : Lawful s) (accepted : advance s request = some next)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Entry) (found : s.rows[index]? = some origin) :
    origin.1 ∈ next.rows.map Prod.fst ↔ index ∉ request.2.1 := by
  obtain ⟨view, published, same⟩ := Option.map_eq_some_iff.mp accepted
  cases same
  have grant := (apply_admitted s.view request view published).1
  have original := List.mem_of_getElem? found
  have kept := contract_sublist (mask s.view request.2.1) s.rows
  simp only [transport, List.map_append, List.mem_append]
  constructor
  · rintro (retained | created)
    · obtain ⟨other, member, equal⟩ := List.mem_map.mp retained
      have sameOrigin := List.inj_on_of_nodup_map lawful.2.1 (kept.subset member) original equal
      exact (retained_at_iff s request lawful index origin found).mp (sameOrigin ▸ member)
    · obtain ⟨other, member, equal⟩ := List.mem_map.mp created
      have oldAge := (lawful.2.2 origin original).2
      have newAge := (fresh_age s.view _ _ _ other member).2
      have sameAge := congrArg (fun id : StoreOccurrenceId StoreId Nat => id.read.revision) equal
      omega
  · intro unchosen
    exact Or.inl (List.mem_map.mpr ⟨origin, (retained_at_iff s request lawful index origin found).mpr unchosen, rfl⟩)

/-- A retained name still carries the identical original payload at its new
current position in the actual published view. -/
theorem advance_keeps_origin [DecidableEq StoreId] (s next : WithOrigins StoreId Entry)
    (request : Request StoreId Entry) (lawful : Lawful s) (accepted : advance s request = some next)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Entry) (found : s.rows[index]? = some origin)
    (unchosen : index ∉ request.2.1) :
    ∃ target : Nat, next.rows[target]? = some origin ∧ next.view.entries[target]? = some origin.2 := by
  have member : origin ∈ next.rows := by
    obtain ⟨view, _, same⟩ := Option.map_eq_some_iff.mp accepted
    cases same
    exact List.mem_append_left _ ((retained_at_iff s request lawful index origin found).mpr unchosen)
  obtain ⟨target, located⟩ := List.getElem?_of_mem member
  refine ⟨target, located, ?_⟩
  rw [← (advance_lawful s next request lawful accepted).1.1, List.getElem?_map, located]
  rfl

/-- An absent old name cannot return under any later finite publication.
The only new names come from strictly newer revisions; no history is stored. -/
theorem run_no_reintroduced_name [DecidableEq StoreId] (requests : List (Request StoreId Entry))
    (s final : WithOrigins StoreId Entry) (lawful : Lawful s) (accepted : run requests s = some final)
    (old : StoreOccurrenceId StoreId Nat) (age : old.read.revision ≤ s.view.revision)
    (absent : old ∉ s.rows.map Prod.fst) : old ∉ final.rows.map Prod.fst := by
  induction requests generalizing s with
  | nil => cases Option.some.inj accepted; exact absent
  | cons request rest ih =>
      obtain ⟨next, moved, continued⟩ := Option.bind_eq_some_iff.mp accepted
      have progress := advance_lawful s next request lawful moved
      have noNext : old ∉ next.rows.map Prod.fst := by
        obtain ⟨view, published, same⟩ := Option.map_eq_some_iff.mp moved
        cases same
        have grant := (apply_admitted s.view request view published).1
        simp only [transport, List.map_append, List.mem_append, not_or]
        constructor
        · exact fun member => absent (((contract_sublist _ _).map Prod.fst).subset member)
        · intro member
          obtain ⟨origin, freshMember, equal⟩ := List.mem_map.mp member
          have freshAge := (fresh_age s.view _ _ _ origin freshMember).2
          have sameAge := congrArg (fun id : StoreOccurrenceId StoreId Nat => id.read.revision) equal
          omega
      exact ih next progress.1 continued (Nat.le_trans age (Nat.le_of_lt progress.2.1)) noNext

/-- Once an actually selected surviving origin is spent, no later finite
publication can recreate its name, even by returning an equal payload. -/
theorem consumed_name_stays_spent [DecidableEq StoreId] (s next final : WithOrigins StoreId Entry)
    (request : Request StoreId Entry) (rest : List (Request StoreId Entry)) (lawful : Lawful s)
    (advanced : advance s request = some next) (continued : run rest next = some final)
    (index : Nat) (origin : StoreOccurrenceId StoreId Nat × Entry)
    (found : s.rows[index]? = some origin) (chosen : index ∈ request.2.1) :
    origin.1 ∉ final.rows.map Prod.fst := by
  have progress := advance_lawful s next request lawful advanced
  have age := (lawful.2.2 origin (List.mem_of_getElem? found)).2
  have removed : origin.1 ∉ next.rows.map Prod.fst := by
    intro retained
    exact ((advance_name_iff s next request lawful advanced index origin found).mp retained) chosen
  exact run_no_reintroduced_name rest next final progress.1 continued origin.1
    (Nat.le_trans age (Nat.le_of_lt progress.2.1)) removed

/-- Starting from the actual source enumeration constructs the invariant;
no caller-supplied source/origin equality is needed for this finite result. -/
theorem run_from_initial [DecidableEq StoreId] (requests : List (Request StoreId Entry))
    (view : RevisionedStoreView StoreId Nat Entry) (final : WithOrigins StoreId Entry)
    (accepted : run requests (initial view) = some final) :
    runViews requests view = some final.view ∧ Lawful final ∧
      view.revision ≤ final.view.revision ∧ final.view.storeId = view.storeId := by
  have erased := run_erasure requests (initial view)
  rw [accepted] at erased
  have result := run_lawful requests (initial view) final (initial_lawful view) accepted
  exact ⟨erased.symm, result.1, result.2.1, result.2.2⟩

namespace Controls

private def source : RevisionedStoreView Nat Nat Nat := ⟨1, 7, [42, 42, 99]⟩
private def requests : List (Request Nat Nat) :=
  [(⟨1, 7⟩, [0], [42], 8), (⟨1, 8⟩, [0], [42, 42], 9), (⟨1, 9⟩, [1], [], 10)]

/-- Three real publications shift addresses twice. The second old equal input
and a later fresh input are consumed at their actual new positions. -/
theorem duplicate_payload_shifted_consumption :
    (run requests (initial source)).map (fun s => (s.view.entries, s.rows.map Prod.fst, s.view.revision)) =
      some ([99, 42, 42], [source.occurrenceId 2, ⟨⟨1, 9⟩, 2⟩, ⟨⟨1, 9⟩, 3⟩], 10) := by decide

/-- The one-cut contract alone permits going back to an old unequal revision;
the constructed compositional discipline refuses it and stale equal data. -/
theorem reused_revision_and_equal_restore_refused :
    let restored := source.replaceRevision 8 source.entries
    (publish restored restored.readToken [] [] 7).isSome = true ∧
      (apply restored (restored.readToken, [], [], 7)).isNone = true ∧
      (apply restored (source.readToken, [0], [42], 9)).isNone = true := by decide

end Controls

#print axioms initial_lawful
#print axioms advance_lawful
#print axioms run_erasure
#print axioms run_append
#print axioms run_lawful
#print axioms later_fresh_ne_earlier
#print axioms reused_revision_refused
#print axioms advance_name_iff
#print axioms advance_keeps_origin
#print axioms run_no_reintroduced_name
#print axioms consumed_name_stays_spent
#print axioms run_from_initial
#print axioms Controls.duplicate_payload_shifted_consumption
#print axioms Controls.reused_revision_and_equal_restore_refused

end RevisionedStoreView.Publication.Finite

/-! ## Positive and negative discriminators -/

private def duplicateView : RevisionedStoreView Unit Nat Nat :=
  ⟨(), 7, [42, 42]⟩

example : duplicateView.resolve (duplicateView.occurrenceId 0) = some 42 := by
  rfl

example : duplicateView.occurrenceId 0 ≠ duplicateView.occurrenceId 1 := by
  exact duplicateView.occurrenceId_injective (by decide)

example :
    (duplicateView.replaceRevision 8 [42]).resolve
      (duplicateView.occurrenceId 0) = none := by
  exact duplicateView.old_occurrence_rejected_after_revision_change
    8 [42] (by decide) 0

/-- Candidate permutation is sufficient for an exhaustive occurrence bag,
but not for ordered or finite-prefix observations. -/
example :
    [duplicateView.occurrenceId 0, duplicateView.occurrenceId 1].Perm
      [duplicateView.occurrenceId 1, duplicateView.occurrenceId 0] := by
  exact List.Perm.swap _ _ []

example :
    [duplicateView.occurrenceId 0, duplicateView.occurrenceId 1] ≠
      [duplicateView.occurrenceId 1, duplicateView.occurrenceId 0] := by
  simp [RevisionedStoreView.occurrenceId,
    RevisionedStoreView.readToken, duplicateView]

/-! ## Compiling stable keys to current positional publication

The reference removes by key equality. The adapter computes current positions
from the actual finite row list and calls the existing checked publication.
A previous read token is never refreshed by this compilation.
-/

namespace RevisionedStoreView.Publication.Keyed

variable {StoreId Revision Entry Key : Type} [DecidableEq Key]

/-- Missing keys compile to the list length and fail positional admission. -/
def index (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry) (key : Key) : Nat :=
  (view.entries.map identity).idxOf key

def positions (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (chosen : List Key) : List Nat := chosen.map (index identity view)

def remaining (identity : Entry → Key) (rows : List Entry) (chosen : List Key) : List Entry :=
  rows.filter fun row => decide (identity row ∉ chosen)

/-- Independent keyed list semantics, with no positional compiler. -/
def reference (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (chosen : List Key) (outputs : List Entry) (nextRevision : Revision) :
    RevisionedStoreView StoreId Revision Entry :=
  view.replaceRevision nextRevision (remaining identity view.entries chosen ++ outputs)

def publish [DecidableEq StoreId] [DecidableEq Revision]
    (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (read : StoreReadToken StoreId Revision) (chosen : List Key)
    (outputs : List Entry) (nextRevision : Revision) : Option (RevisionedStoreView StoreId Revision Entry) :=
  if (view.entries.map identity).Nodup then
    Publication.publish view read (positions identity view chosen) outputs nextRevision
  else none

theorem index_of_found (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (unique : (view.entries.map identity).Nodup) (index : Nat) (row : Entry)
    (found : view.entries[index]? = some row) :
    (view.entries.map identity).idxOf (identity row) = index := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  have mapped : (view.entries.map identity)[index]? = some (identity row) := by
    rw [List.getElem?_map, found]
    rfl
  have actual := unique.idxOf_getElem index (by simpa using bound)
  rw [(List.getElem?_eq_some_iff.mp mapped).2] at actual
  exact actual

theorem lookup_key (view : RevisionedStoreView StoreId Revision Key) (key : Key)
    (present : key ∈ view.entries) : view.entries[index id view key]? = some key := by
  simpa only [index, List.map_id] using List.getElem?_idxOf present

theorem select_exact (view : RevisionedStoreView StoreId Revision Key) (chosen : List Key)
    (present : ∀ key ∈ chosen, key ∈ view.entries) :
    (positions id view chosen).filterMap (fun i => view.entries[i]?) = chosen := by
  induction chosen with
  | nil => rfl
  | cons key rest ih =>
      have tail : ∀ key ∈ rest, key ∈ view.entries := fun key member => present key (List.mem_cons_of_mem _ member)
      change (match view.entries[index id view key]? with
        | none => (positions id view rest).filterMap (fun i => view.entries[i]?)
        | some row => row :: (positions id view rest).filterMap (fun i => view.entries[i]?)) = key :: rest
      rw [lookup_key view key (present key List.mem_cons_self)]
      exact congrArg (List.cons key) (ih tail)

theorem selected_iff (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (unique : (view.entries.map identity).Nodup) (chosen : List Key)
    (index : Nat) (row : Entry) (found : view.entries[index]? = some row) :
    index ∈ positions identity view chosen ↔ identity row ∈ chosen := by
  have located := index_of_found identity view unique index row found
  constructor
  · intro member
    obtain ⟨key, selected, same⟩ := List.mem_map.mp member
    have present : identity row ∈ view.entries.map identity := List.mem_map.mpr ⟨row, List.mem_of_getElem? found, rfl⟩
    have equal := (List.idxOf_inj present).mp (located.trans same.symm)
    exact equal.symm ▸ selected
  · intro selected
    exact List.mem_map.mpr ⟨identity row, selected, located⟩

/-- The positional mask and the independent key predicate agree at every
actual source occurrence, including different rows with equal payloads. -/
theorem contraction_eq_remaining (identity : Entry → Key)
    (view : RevisionedStoreView StoreId Revision Entry)
    (unique : (view.entries.map identity).Nodup) (chosen : List Key) :
    (contracted view (positions identity view chosen)).rows = remaining identity view.entries chosen := by
  have masks : mask view (positions identity view chosen) =
      view.entries.map (fun row => decide (identity row ∉ chosen)) := by
    simp only [mask, occurrences, occurrenceId, List.map_map, Function.comp_def]
    calc
      _ = view.entries.zipIdx.map (fun pair => decide (identity pair.1 ∉ chosen)) := by
        apply List.map_congr_left
        intro pair member
        have found := getElem?_eq_some_of_mem_zipIdx member
        simp only [selected_iff identity view unique chosen pair.2 pair.1 found]
      _ = _ := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (fun row => decide (identity row ∉ chosen))) (List.zipIdx_map_fst 0 view.entries)
  simp only [contracted, Mettapedia.GSLT.Dynamics.StableOccurrenceContraction.compile_rows_exact, masks,
    contract_predicate, remaining]

theorem admitted [DecidableEq StoreId] [DecidableEq Revision]
    (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (read : StoreReadToken StoreId Revision) (chosen : List Key) (outputs : List Entry)
    (nextRevision : Revision) (result : RevisionedStoreView StoreId Revision Entry)
    (accepted : publish identity view read chosen outputs nextRevision = some result) :
    (view.entries.map identity).Nodup ∧ read = view.readToken ∧ chosen.Nodup ∧
      (∀ key ∈ chosen, key ∈ view.entries.map identity) ∧ nextRevision ≠ view.revision ∧
      result = reference identity view chosen outputs nextRevision := by
  unfold publish at accepted
  split at accepted
  · rename_i unique
    obtain ⟨current, distinct, bounded, fresh, resultEq⟩ :=
      publication_admitted view read (positions identity view chosen) outputs nextRevision result accepted
    refine ⟨unique, current, List.Nodup.of_map _ distinct, ?_, fresh, ?_⟩
    · intro key member
      have bound := bounded ((view.entries.map identity).idxOf key) (List.mem_map.mpr ⟨key, member, rfl⟩)
      exact List.idxOf_lt_length_iff.mp (by simpa using bound)
    · rw [resultEq]
      simp only [updated, reference, contraction_eq_remaining identity view unique]
  · contradiction

/-- No stale token, absent key or repeated selected key can be repaired by
recomputing indices. Source and request injectivity are checked by the adapter. -/
theorem stale_refused [DecidableEq StoreId] [DecidableEq Revision]
    (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (read : StoreReadToken StoreId Revision) (chosen : List Key) (outputs : List Entry)
    (nextRevision : Revision) (stale : read ≠ view.readToken) :
    publish identity view read chosen outputs nextRevision = none := by
  simp [publish, stale_publication_refused view read _ outputs nextRevision stale]

theorem malformed_refused [DecidableEq StoreId] [DecidableEq Revision]
    (identity : Entry → Key) (view : RevisionedStoreView StoreId Revision Entry)
    (read : StoreReadToken StoreId Revision) (chosen : List Key) (outputs : List Entry)
    (nextRevision : Revision)
    (bad : ¬ (view.entries.map identity).Nodup ∨ ¬ chosen.Nodup ∨
      ∃ key ∈ chosen, key ∉ view.entries.map identity) :
    publish identity view read chosen outputs nextRevision = none := by
  cases result : publish identity view read chosen outputs nextRevision with
  | none => rfl
  | some next =>
      have valid := admitted identity view read chosen outputs nextRevision next result
      rcases bad with bad | bad | ⟨key, selected, missing⟩
      · exact False.elim (bad valid.1)
      · exact False.elim (bad valid.2.2.1)
      · exact False.elim (missing (valid.2.2.2.1 key selected))

#print axioms index_of_found
#print axioms lookup_key
#print axioms select_exact
#print axioms selected_iff
#print axioms contraction_eq_remaining
#print axioms admitted
#print axioms stale_refused
#print axioms malformed_refused

end RevisionedStoreView.Publication.Keyed


/-! ## Projected immutable snapshots and finite page assembly

The projection profile yields at most one row for each stored occurrence.
A matching service with several results per occurrence needs its own projection
instance. Projected rows retain order and multiplicity, not physical input IDs.
-/
namespace RevisionedStoreView.Snapshot

variable {StoreId Entry Row : Type}

def capture (source : RevisionedStoreView StoreId Nat Entry) (project : Entry → Option Row) :
    RevisionedStoreView StoreId Nat Row :=
  ⟨source.storeId, source.revision, source.entries.filterMap project⟩

abbrev Prefix (StoreId Row : Type) := List Row × OwnedFork.Cursor StoreId Row

def start (snapshot : RevisionedStoreView StoreId Nat Row) : Prefix StoreId Row :=
  ([], ⟨snapshot, 0⟩)

/-- Iterate the existing cursor, retaining the complete unconsumed suffix. -/
def fetch : Nat → Prefix StoreId Row → Prefix StoreId Row
  | 0, state => state
  | n + 1, state => match state.2.step with
    | none => state
    | some (row, rest) => fetch n (state.1 ++ [row], rest)

def ready (state : Prefix StoreId Row) : Bool :=
  decide (state.2.next = state.2.captured.entries.length)

def Lawful (snapshot : RevisionedStoreView StoreId Nat Row) (state : Prefix StoreId Row) : Prop :=
  state.2.captured = snapshot ∧ state.2.next ≤ snapshot.entries.length ∧
    state.1 = snapshot.entries.take state.2.next

@[simp] theorem capture_read (source : RevisionedStoreView StoreId Nat Entry) (project : Entry → Option Row) :
    (capture source project).readToken = source.readToken := rfl

theorem fetch_stopped (n : Nat) (state : Prefix StoreId Row) (stopped : state.2.step = none) :
    fetch n state = state := by
  cases n <;> simp [fetch, stopped]

/-- Exact state splitting includes both the accumulated prefix and cursor. -/
theorem fetch_split (first second : Nat) (state : Prefix StoreId Row) :
    fetch second (fetch first state) = fetch (first + second) state := by
  induction first generalizing state with
  | zero => simp [fetch]
  | succ first ih =>
      cases found : state.2.step with
      | none => simp [fetch_stopped, found, Nat.succ_add, fetch]
      | some pair => simpa [Nat.succ_add, fetch, found] using ih (state.1 ++ [pair.1], pair.2)

/-- The actual iterative page is exactly the requested captured list slice. -/
theorem fetch_exact (n : Nat) (state : Prefix StoreId Row) :
    (fetch n state).1 = state.1 ++ state.2.read n ∧
    (fetch n state).2.captured = state.2.captured ∧
    (fetch n state).2.next = state.2.next + (state.2.read n).length := by
  induction n generalizing state with
  | zero => simp [fetch, OwnedFork.Cursor.read]
  | succ n ih =>
      cases found : state.2.captured.entries[state.2.next]? with
      | none => simp [fetch, OwnedFork.Cursor.step, OwnedFork.Cursor.read, found]
      | some row =>
          have later := ih (state.1 ++ [row], ⟨state.2.captured, state.2.next + 1⟩)
          simpa [fetch, OwnedFork.Cursor.step, OwnedFork.Cursor.read, found, List.append_assoc,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using later

theorem start_lawful (snapshot : RevisionedStoreView StoreId Nat Row) : Lawful snapshot (start snapshot) := by
  simp [Lawful, start]

theorem fetch_lawful (n : Nat) (snapshot : RevisionedStoreView StoreId Nat Row)
    (state : Prefix StoreId Row) (safe : Lawful snapshot state) : Lawful snapshot (fetch n state) := by
  obtain ⟨captured, bound, accumulated⟩ := safe
  obtain ⟨rows, same, position⟩ := fetch_exact n state
  rw [OwnedFork.cursor_prefix, captured] at rows position
  refine ⟨same.trans captured, ?_, ?_⟩
  · rw [position, List.length_take, List.length_drop]
    omega
  · rw [rows, accumulated, position, ← List.take_add]
    apply List.take_eq_take_iff.mpr
    simp only [List.length_take, List.length_drop]
    omega

/-- No unread rows are discarded to manufacture a complete snapshot. -/
theorem completed_rows (snapshot : RevisionedStoreView StoreId Nat Row) (state : Prefix StoreId Row)
    (safe : Lawful snapshot state) (complete : ready state = true) : state.1 = snapshot.entries := by
  have position : state.2.next = snapshot.entries.length := by
    simpa [ready, safe.1] using complete
  simpa [position] using safe.2.2

theorem fetch_prefix (snapshot : RevisionedStoreView StoreId Nat Row) (count : Nat) :
    (fetch count (start snapshot)).1 = snapshot.entries.take count ∧
    (fetch count (start snapshot)).2.next = min count snapshot.entries.length ∧
    (fetch count (start snapshot)).2.captured = snapshot := by
  simpa [start, OwnedFork.cursor_prefix] using
    (show (fetch count (start snapshot)).1 = [] ++ (start snapshot).2.read count ∧
      (fetch count (start snapshot)).2.next = 0 + ((start snapshot).2.read count).length ∧
      (fetch count (start snapshot)).2.captured = snapshot from
      ⟨(fetch_exact count (start snapshot)).1, (fetch_exact count (start snapshot)).2.2,
        (fetch_exact count (start snapshot)).2.1⟩)

/-- The old source is preserved in order; every output is appended once.
The whole-source token is required even when only a projection was read. -/
theorem append_only [DecidableEq StoreId]
    (current : RevisionedStoreView StoreId Nat Entry) (read : StoreReadToken StoreId Nat)
    (outputs : List Entry) (next : Nat) :
    Publication.publish current read [] outputs next =
      if read = current.readToken ∧ next ≠ current.revision then
        some (current.replaceRevision next (current.entries ++ outputs)) else none := by
  simp only [Publication.publish, List.nodup_nil, List.not_mem_nil, false_implies, implies_true,
    true_and]
  congr 1
  have keep_all : ∀ rows : List Entry,
      Mettapedia.GSLT.Dynamics.StableOccurrenceContraction.contract
        (List.replicate rows.length true) rows = rows := by
    intro rows
    induction rows with
    | nil => rfl
    | cons row rest ih =>
        simp [List.replicate_succ, Mettapedia.GSLT.Dynamics.StableOccurrenceContraction.contract, ih]
  simp [Publication.updated, Publication.contracted, Publication.mask, occurrences,
    Mettapedia.GSLT.Dynamics.StableOccurrenceContraction.compile_rows_exact, keep_all]

#print axioms capture_read
#print axioms fetch_split
#print axioms fetch_exact
#print axioms start_lawful
#print axioms fetch_lawful
#print axioms completed_rows
#print axioms fetch_prefix
#print axioms append_only

end RevisionedStoreView.Snapshot

end Mettapedia.Machines
