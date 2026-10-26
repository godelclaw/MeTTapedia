import Mettapedia.Machines.SpaceService
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# Conservative observations over a revisioned native store

The first transaction implementation validates a whole-store revision. A scope
may denote a key, range, arbitrary matching predicate, or an empty answer. No
positive-read shortcut is used. This module supplies the missing argument that
equal revisions imply equal state along a valid store history, then connects
that argument to the atomic snapshot transaction interface.

Rows are the portable keys of `SpaceService`; occurrence order and duplicates
are retained. The value codec, native matching, journal publication, and absence
of out-of-band mutation are separate implementation obligations. The MeTTa
client (`space:observe`, `space:commit`) is checked by trace replay; these laws
alone are not a proof of its interpreter or filesystem implementation.
-/

namespace Mettapedia.Machines.NativeStoreTransactions

open SpaceService
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction (Spec Matches)

inductive Mutation where
  | add (row : Nat)
  | remove (row : Nat)
deriving DecidableEq, Repr

def Mutation.row : Mutation → Nat
  | .add row | .remove row => row

def Mutation.apply (rows : List Nat) : Mutation → List Nat
  | .add row => rows ++ [row]
  | .remove row => rows.erase row

def applyBatch (rows : List Nat) (operations : List Mutation) : List Nat :=
  operations.foldl Mutation.apply rows

/-- None is a rejection; some target is one complete accepted publication. -/
def history (store : Store) : List (Option (List Nat)) → Store
  | [] => store
  | none :: rest => history store rest
  | some rows :: rest =>
      history { store with revision := store.revision + 1, rows := rows } rest

theorem history_revision_monotone (store : Store) (steps : List (Option (List Nat))) :
    store.revision ≤ (history store steps).revision := by
  induction steps generalizing store with
  | nil => exact Nat.le_refl _
  | cons step rest ih =>
    cases step with
    | none => exact ih store
    | some rows =>
      exact Nat.le_trans (Nat.le_add_right _ 1)
        (ih { store with revision := store.revision + 1, rows := rows })

/-- Revision validation is sound because every accepted publication advances,
including no-ops. This would be false with revision reuse or hidden mutation. -/
theorem unchanged_revision_preserves_state (store : Store)
    (steps : List (Option (List Nat)))
    (same : (history store steps).revision = store.revision) :
    history store steps = store := by
  induction steps generalizing store with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | none => exact ih store same
    | some rows =>
      have monotone := history_revision_monotone
        { store with revision := store.revision + 1, rows := rows } rest
      simp only [history] at same
      simp only at monotone
      omega

abbrev Scope := Nat → Bool

def observe (scope : Scope) (store : Store) : List Nat := store.rows.filter scope

theorem validated_observation_is_current (scope : Scope) (store : Store)
    (steps : List (Option (List Nat)))
    (same : (history store steps).revision = store.revision) :
    observe scope (history store steps) = observe scope store := by
  rw [unchanged_revision_preserves_state store steps same]

theorem validated_absence_is_current (scope : Scope) (store : Store)
    (steps : List (Option (List Nat)))
    (same : (history store steps).revision = store.revision)
    (absent : observe scope store = []) :
    observe scope (history store steps) = [] := by
  rw [validated_observation_is_current scope store steps same, absent]

/-- Each read may occur at a different time. If all carry the initial revision,
all their complete ordered answers belong to the same captured state. -/
theorem separately_read_scopes_are_coherent (store : Store)
    (reads : List (Scope × List (Option (List Nat))))
    (validated : ∀ read ∈ reads,
      (history store read.2).revision = store.revision) :
    reads.map (fun read => observe read.1 (history store read.2)) =
      reads.map (fun read => observe read.1 store) := by
  apply List.map_congr_left
  intro read member
  exact validated_observation_is_current read.1 store read.2 (validated read member)

structure Proposal where
  captured : Store
  writes : Scope
  operations : List Mutation

def covered (proposal : Proposal) : Bool :=
  proposal.operations.all (fun op => proposal.writes op.row)

inductive Rejection | identity | stale | scope
deriving DecidableEq, Repr

def commit (live : Store) (proposal : Proposal) : Except Rejection Store :=
  if !covered proposal then .error .scope
  else if live.identity ≠ proposal.captured.identity then .error .identity
  else if live.revision ≠ proposal.captured.revision then .error .stale
  else .ok { live with
    revision := live.revision + 1
    rows := applyBatch live.rows proposal.operations }

def visibleAfter (live : Store) (proposal : Proposal) : Store :=
  match commit live proposal with
  | .error _ => live
  | .ok next => next

theorem rejection_preserves_state (live : Store) (proposal : Proposal)
    (reason : Rejection) (rejected : commit live proposal = .error reason) :
    visibleAfter live proposal = live := by simp [visibleAfter, rejected]

theorem committed_batch_is_whole (live next : Store) (proposal : Proposal)
    (accepted : commit live proposal = .ok next) :
    next = { live with revision := live.revision + 1,
                       rows := applyBatch live.rows proposal.operations } := by
  unfold commit at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · exact (Except.ok.inj accepted).symm

theorem commit_requires_all_write_scopes (live next : Store) (proposal : Proposal)
    (accepted : commit live proposal = .ok next) :
    ∀ op ∈ proposal.operations, proposal.writes op.row = true := by
  unfold commit at accepted
  split at accepted
  · cases accepted
  · rename_i scope
    simpa [covered] using scope

def atomicSpec : Spec (Nat × Nat) (List Nat) Mutation Proposal where
  capturedRevision p := (p.captured.identity, p.captured.revision)
  capturedState p := p.captured.rows
  targetState p := applyBatch p.captured.rows p.operations
  pendingWork p := p.operations

/-- Native revision validation discharges BOTH fields required by the generic
atomic interface, rather than assuming state agreement from an arbitrary token. -/
theorem revision_validation_refines_atomic_match (proposal : Proposal)
    (steps : List (Option (List Nat)))
    (same : (history proposal.captured steps).revision = proposal.captured.revision) :
    Matches atomicSpec proposal
      ⟨((history proposal.captured steps).identity,
         (history proposal.captured steps).revision),
        (history proposal.captured steps).rows⟩ := by
  rw [unchanged_revision_preserves_state proposal.captured steps same]
  exact ⟨rfl, rfl⟩

theorem duplicate_occurrences_are_preserved :
    applyBatch [] [.add 7, .add 7, .remove 7] = [7] := by decide

theorem negative_dependency_control :
    let initial : Store := ⟨1, 0, []⟩
    let changed := history initial [some [7]]
    observe (· == 7) initial = [] ∧ observe (· == 7) changed = [7] ∧
      commit changed ⟨initial, fun _ => true, [.add 9]⟩ = .error .stale := by decide

theorem no_op_invalidates_an_old_proposal :
    let initial : Store := ⟨1, 0, [7, 7]⟩
    commit (history initial [some [7, 7]])
      ⟨initial, fun _ => true, []⟩ = .error .stale := by decide

theorem undeclared_write_cannot_partially_publish :
    let initial : Store := ⟨1, 0, []⟩
    let proposal : Proposal := ⟨initial, (· == 7), [.add 7, .add 8]⟩
    commit initial proposal = .error .scope ∧
      visibleAfter initial proposal = initial := by decide

/-! The executable trace adapter uses exactly the definitions above. It is
fed the same finite commands as the MeTTa client and the SQLite test oracle. -/

inductive WriteScope | all | only (row : Nat)
deriving Repr

def WriteScope.admits : WriteScope → Scope
  | .all => fun _ => true
  | .only row => (· == row)

inductive TraceCommand where
  | observe (name : Nat) (scope : WriteScope)
  | external (operations : List Mutation)
  | commit (name : Nat) (operations : List Mutation)
deriving Repr

structure TraceState where
  store : Store := ⟨1, 0, []⟩
  observations : List (Nat × Store × WriteScope) := []

def traceStep (state : TraceState) (command : TraceCommand) : String × TraceState :=
  match command with
  | .observe name scope =>
      ("observed", { state with observations := (name, state.store, scope) :: state.observations })
  | .external operations =>
      ("external", { state with store := { state.store with
        revision := state.store.revision + 1
        rows := applyBatch state.store.rows operations } })
  | .commit name operations =>
      match state.observations.find? (fun item => item.1 == name) with
      | none => ("missing", state)
      | some (_, captured, scope) =>
          match commit state.store ⟨captured, scope.admits, operations⟩ with
          | .ok next => ("committed", { state with store := next })
          | .error .identity => ("identity", state)
          | .error .scope => ("scope", state)
          | .error .stale => ("stale", state)

def traceLines (state : TraceState) : List TraceCommand → List String
  | [] => []
  | command :: rest =>
      let (status, next) := traceStep state command
      (status ++ "|" ++ toString next.store.revision ++ "|" ++ reprStr next.store.rows) ::
        traceLines next rest

end Mettapedia.Machines.NativeStoreTransactions
