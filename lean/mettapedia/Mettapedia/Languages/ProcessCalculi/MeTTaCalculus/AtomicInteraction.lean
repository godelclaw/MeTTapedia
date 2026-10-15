import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# Publishing a prepared guarded interaction

A private interaction retains its captured world, selected occurrence vector,
shared binding environment and exact consumed residual. Its target is computed
by the existing continuation publication operation. The atomic snapshot layer
then validates the captured world before exposing that target.

The same construction covers explicit work directives and binary contact.
It fixes neither search order nor retry policy. Full-snapshot validation is a
conservative boundary; a dependency-based validator needs its own theorem.
These are semantic receipts, not an implementation of a concurrent store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.AtomicInteraction

open SpaceInteraction SpaceInteraction.GuardedTransaction
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction

universe uRevision uLocation uAtom uPattern uEnvironment

variable {Revision : Type uRevision} {Location : Type uLocation}
variable {Atom : Type uAtom} {Pattern : Type uPattern} {Environment : Type uEnvironment}
variable [DecidableEq Location]

/-- Prepared work carries primitive matching and access witnesses. It does
not manufacture an authority to publish its captured world. -/
structure Prepared (Revision : Type uRevision) (Location : Type uLocation)
    (Atom : Type uAtom) (Pattern : Type uPattern) (Environment : Type uEnvironment)
    [DecidableEq Location]
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop) where
  captured : Snapshot Revision (Network Location Atom)
  command : Command Location Atom Pattern Environment
  permitted : enabled command
  atoms : List Atom
  environment : Environment
  residual : Network Location Atom
  selected : selects command.guards atoms environment
  observed : ObservesSnapshot command.guards atoms captured.state
  consumed : Consumes command.guards atoms captured.state residual

namespace Prepared

variable {selects : Selection Location Atom Pattern Environment}
variable {enabled : Command Location Atom Pattern Environment → Prop}

/-- The complete target is calculated from the retained environment and the
source continuation, rather than supplied as an unrelated result. -/
def target (work : Prepared Revision Location Atom Pattern Environment selects enabled) :
    Network Location Atom :=
  publishAll (work.command.continuation work.environment) work.residual

theorem fires (work : Prepared Revision Location Atom Pattern Environment selects enabled) :
    Fires selects work.command work.captured.state work.target :=
  .fire work.selected work.observed work.consumed

/-- Matching retains one selected atom for every guard position. In
particular a receipt cannot truncate a repeated premise by zipping lists of
different lengths. -/
theorem occurrence_lengths
    (work : Prepared Revision Location Atom Pattern Environment selects enabled) :
    work.command.guards.length = work.atoms.length := by
  have same : ∀ {guards : List (Guard Location Pattern)} {atoms : List Atom}
      {source : Network Location Atom}, ObservesSnapshot guards atoms source →
        guards.length = atoms.length := by
    intro guards atoms source observed
    induction observed with
    | nil => rfl
    | observe present tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih
    | consume tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih
  exact same work.observed

/-- Each work position retains its guard and selected atom. Equal atoms at
different guard positions remain two ordered entries. -/
def occurrences (work : Prepared Revision Location Atom Pattern Environment selects enabled) :
    List (Guard Location Pattern × Atom) :=
  work.command.guards.zip work.atoms

theorem occurrences_length
    (work : Prepared Revision Location Atom Pattern Environment selects enabled) :
    work.occurrences.length = work.command.guards.length := by
  simp only [occurrences, List.length_zip, ← work.occurrence_lengths, Nat.min_self]

end Prepared

/-- Read the atomic coordinates directly from the actual prepared
interaction. This reuses the existing snapshot validator and receipt ledger. -/
def spec (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop) :
    Spec Revision (Network Location Atom) (Guard Location Pattern × Atom)
      (Prepared Revision Location Atom Pattern Environment selects enabled) where
  capturedRevision work := work.captured.revision
  capturedState work := work.captured.state
  targetState work := work.target
  pendingWork work := work.occurrences

section Publication

variable {selects : Selection Location Atom Pattern Environment}
variable {enabled : Command Location Atom Pattern Environment → Prop}
variable {work sibling : Prepared Revision Location Atom Pattern Environment selects enabled}
variable {live : Snapshot Revision (Network Location Atom)}

/-- A committed interaction is an actual transition of the guarded GSLT
from the live source, including all continuation emissions. The result is
derived from matching, observation and consumption, not an assumed whole
interaction soundness interface. -/
theorem committed_is_source_step (receipt : CommitReceipt (spec selects enabled) work live) :
    (theory selects enabled).Step live.state receipt.after.state := by
  change ∃ command, enabled command ∧ Fires selects command live.state work.target
  refine ⟨work.command, work.permitted, ?_⟩
  have current : live.state = work.captured.state := receipt.current.state_eq
  rw [current]
  exact work.fires

/-- Every guard occurrence is accounted for once, in its authored order. -/
theorem committed_retains_occurrence_positions
    (receipt : CommitReceipt (spec selects enabled) work live) :
    (Decision.committed receipt).orderedLedger.executed = work.occurrences ∧
      (Decision.committed receipt).orderedLedger.executed.length = work.command.guards.length ∧
      (Decision.committed receipt).orderedLedger.pending = [] := by
  exact ⟨rfl, work.occurrences_length, rfl⟩

/-- Publication cannot validate another proposal captured at the old
revision. Its private derivation remains evidence of an alternative, not
permission to apply it to the successor world. -/
theorem committed_rejects_captured_sibling
    (receipt : CommitReceipt (spec selects enabled) work live)
    (sameRevision : sibling.captured.revision = work.captured.revision) :
    ¬ Nonempty (CommitReceipt (spec selects enabled) sibling receipt.after) := by
  rintro ⟨nextReceipt⟩
  exact receipt.after_rejects_same_revision_sibling sameRevision nextReceipt.current

/-- A conflict preserves the live world and every pending occurrence.
Retry or reconciliation is a later controller decision. -/
theorem conflict_retains_world_and_work
    (conflict : ¬ Matches (spec selects enabled) work live) :
    (Decision.deferred conflict).physicalSnapshot = live ∧
      (Decision.deferred conflict).orderedLedger.executed = [] ∧
      (Decision.deferred conflict).orderedLedger.pending = work.occurrences :=
  ⟨rfl, rfl, rfl⟩

end Publication

namespace Controls

open SpaceInteraction.GuardedTransaction.Canary

/-- A two-party contact with both source continuations retained. -/
def contact : Prepared Nat CanaryLocation CanaryAtom CanaryAtom Unit exactSelection
    (fun command => command = symmetricCommand) where
  captured := ⟨7, contactSource⟩
  command := symmetricCommand
  permitted := rfl
  atoms := [.leftParty, .rightParty]
  environment := ()
  residual := afterBoth
  selected := .cons rfl (.cons rfl .nil)
  observed := .consume (.consume .nil)
  consumed := by
    apply Consumes.consume
    · exact LocatedStep.consume (location := .control) (atom := .leftParty)
        (state := contactSource) ({.rightParty} : SpaceChannelBoundary.Store CanaryAtom) rfl
    · apply Consumes.consume
      · exact LocatedStep.consume (location := .control) (atom := .rightParty)
          (state := afterLeft) 0 (by simp [afterLeft])
      · exact .nil

def contactSpec := spec (Revision := Nat) exactSelection (fun command => command = symmetricCommand)

def contactReceipt : CommitReceipt contactSpec contact contact.captured where
  current := ⟨rfl, rfl⟩
  nextRevision := 8
  advanced := by decide

/-- Positive control: one admitted publication consumes both parties and
publishes both residuals, with both ordered input occurrences accounted for. -/
theorem contact_publishes_both_continuations :
    contactReceipt.after.state .control = 0 ∧
      contactReceipt.after.state .output =
        ({.rightResidual, .leftResidual} : SpaceChannelBoundary.Store CanaryAtom) ∧
      (Decision.committed contactReceipt).orderedLedger.executed.length = 2 := by
  exact ⟨contactTarget_control, contactTarget_output, rfl⟩

/-- Negative control: a second copy of the private contact cannot publish
again after the first receipt. Copying work does not copy currentness. -/
theorem copied_contact_cannot_publish_twice :
    ¬ Nonempty (CommitReceipt contactSpec contact contactReceipt.after) :=
  committed_rejects_captured_sibling contactReceipt rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.AtomicInteraction
