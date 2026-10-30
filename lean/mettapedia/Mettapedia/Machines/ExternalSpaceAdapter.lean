import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# External Space adapter boundaries

Counterexamples and admission contracts for connecting a remote atom service to
an occurrence-based, captured-view Space. The motivating API intake is DAS at
`dac998abe820a5488d151c1a2304363974203b27`: content handles, pattern HandleSets,
and separate execution/cancellation/stream termination events.

These are generic models, not a verification of DAS or a completed CeTTa
adapter. Revision labels in the join model refer to two reads of one source;
equal counters from different peers do not establish a global snapshot.
See also `Machines.SourceSnapshot` for captured versus reopened source reads.
-/

namespace Mettapedia.Machines.ExternalSpaceAdapter

/-! ## Content identity cannot replace occurrence identity -/

structure Occurrence where
  id : Nat
  content : Nat
deriving DecidableEq, Repr

def contentSet (rows : List Occurrence) : List Nat :=
  (rows.map Occurrence.content).eraseDups

def oneOccurrence : List Occurrence := [⟨10, 7⟩]
def twoOccurrences : List Occurrence := [⟨10, 7⟩, ⟨11, 7⟩]

theorem distinct_occurrences_have_equal_content :
    (twoOccurrences.map Occurrence.id).Nodup ∧
      contentSet oneOccurrence = contentSet twoOccurrences ∧
      oneOccurrence.length ≠ twoOccurrences.length := by decide

/-- Neither a smarter client nor a different matcher can reconstruct erased
multiplicity from this content-set projection alone. -/
theorem content_set_cannot_recover_multiplicity :
    ¬ ∃ recover : List Nat → Nat,
      recover (contentSet oneOccurrence) = oneOccurrence.length ∧
        recover (contentSet twoOccurrences) = twoOccurrences.length := by
  rintro ⟨recover, first, second⟩
  have same : contentSet oneOccurrence = contentSet twoOccurrences := by decide
  have collision := congrArg recover same
  rw [first, second] at collision
  simp [oneOccurrence, twoOccurrences] at collision

def occurrenceRows (rows : List Occurrence) : List (Nat × Nat) :=
  rows.map fun row => (row.id, row.content)

theorem occurrence_projection_retains_multiplicity (rows : List Occurrence) :
    (occurrenceRows rows).length = rows.length := by simp [occurrenceRows]

theorem occurrence_projection_separates_the_witness :
    occurrenceRows oneOccurrence ≠ occurrenceRows twoOccurrences := by decide

/-! ## A join can manufacture an answer by reopening one source -/

inductive Revision where
  | before | after
deriving DecidableEq, Repr

def leftPresent : Revision → Bool
  | .before => true
  | .after => false

def rightPresent : Revision → Bool
  | .before => false
  | .after => true

def joinedAt (revision : Revision) : Bool :=
  leftPresent revision && rightPresent revision

def reopenedJoin (leftRevision rightRevision : Revision) : Bool :=
  leftPresent leftRevision && rightPresent rightRevision

theorem mixed_read_manufactures_an_answer :
    reopenedJoin .before .after = true ∧
      joinedAt .before = false ∧ joinedAt .after = false := by decide

def checkedJoin (leftRevision rightRevision : Revision) : Option Bool :=
  if leftRevision = rightRevision then some (reopenedJoin leftRevision rightRevision)
  else none

theorem checked_join_rejects_mixed_source_generations :
    checkedJoin .before .after = none := by decide

theorem checked_join_matches_captured_execution (revision : Revision) :
    checkedJoin revision revision = some (joinedAt revision) := by
  cases revision <;> rfl

/-- No revision evidence cannot be relabelled as a captured-view result.
This is an admission rule; token authenticity is an external obligation. -/
def admitsCaptured (revision : Option Nat) : Bool := revision.isSome

theorem unknown_revision_is_not_captured : admitsCaptured none = false := rfl

/-! ## Socket closure and cancellation requests are not terminal receipts -/

inductive Terminal where
  | completed | aborted | failed
deriving DecidableEq, Repr

structure StreamState where
  received : Nat := 0
  connected : Bool := true
  cancelRequested : Bool := false
  terminal : Option Terminal := none
deriving DecidableEq, Repr

inductive Event where
  | rows (count : Nat)
  | socketClosed
  | requestCancel
  | terminal (result : Terminal)
deriving DecidableEq, Repr

def step (state : StreamState) : Event → StreamState
  | .rows count => { state with received := state.received + count }
  | .socketClosed => { state with connected := false }
  | .requestCancel => { state with cancelRequested := true }
  | .terminal result => { state with terminal := some result }

def completed (state : StreamState) : Bool := state.terminal == some .completed
def remoteSettled (state : StreamState) : Bool := state.terminal.isSome
def legacyClosedMeansDone (state : StreamState) : Bool := !state.connected

theorem socket_close_does_not_establish_completion (count : Nat) :
    let state := step { received := count } .socketClosed
    legacyClosedMeansDone state = true ∧ completed state = false := by
  simp [step, legacyClosedMeansDone, completed]

theorem cancellation_request_is_not_remote_cleanup :
    let state := step {} .requestCancel
    state.cancelRequested = true ∧ remoteSettled state = false ∧ completed state = false := by decide

theorem aborted_is_settled_but_incomplete (count : Nat) :
    let state := step { received := count } (.terminal .aborted)
    remoteSettled state = true ∧ completed state = false := by
  simp [step, remoteSettled, completed]

theorem failed_is_settled_but_incomplete (count : Nat) :
    let state := step { received := count } (.terminal .failed)
    remoteSettled state = true ∧ completed state = false := by
  simp [step, remoteSettled, completed]

theorem empty_complete_and_empty_disconnected_are_distinct :
    (step {} (.terminal .completed)).received = (step {} .socketClosed).received ∧
      completed (step {} (.terminal .completed)) = true ∧
      completed (step {} .socketClosed) = false := by decide

end Mettapedia.Machines.ExternalSpaceAdapter
