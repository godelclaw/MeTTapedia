import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# Atomic context epochs

Source provenance: adapted from GödelClaw commit
`25e339eb66a5447bdaaa735ef9f3bee745b8957d`; only module packaging and
taxonomy-facing names were changed during integration.

A model-visible coding context is meaningful only relative to the operational
workspace and source revisions from which it was built.  Those coordinates
must move together.  In particular, instruction scope must not be resolved
against an implicit process working directory while the view describes a
different task workspace.

This file treats a context epoch as one product value.  A completed refresh
replaces the whole product; failure, interruption, or absence of a completed
candidate leaves the previous epoch live.  Source discovery and compaction are
replaceable policies outside this transition.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.ContextEpoch

open Mettapedia.CognitiveArchitecture.Agent.WorldState

/-- One model-visible context and the exact references under which it was
constructed.  The commitment field is a protected projection, not the
authoritative commitment store. -/
structure Epoch
    (Workspace OperationalRevision InstructionRevision
      CommitmentProjection View : Type*) where
  sequence : Nat
  workspace : Workspace
  operationalRevision : OperationalRevision
  instructionRevision : InstructionRevision
  commitments : CommitmentProjection
  view : View
deriving Repr, DecidableEq

/-- A refresh either produces one complete candidate epoch or fails before
promotion. -/
inductive Refresh (EpochType : Type*) where
  | success (next : EpochType)
  | failure
deriving Repr, DecidableEq

/-- The atomic promotion boundary. -/
def promote (live : EpochType) : Refresh EpochType → EpochType
  | .success next => next
  | .failure => live

@[simp] theorem successful_refresh_replaces_epoch
    (live next : EpochType) :
    promote live (.success next) = next := by
  rfl

@[simp] theorem failed_refresh_preserves_epoch (live : EpochType) :
    promote live .failure = live := by
  rfl

/-- Promotion cannot synthesize a torn mixture: the result is exactly the old
epoch or exactly the completed candidate. -/
theorem promotion_is_atomic (live : EpochType) (refresh : Refresh EpochType) :
    promote live refresh = live ∨
      ∃ next, refresh = .success next ∧ promote live refresh = next := by
  cases refresh with
  | failure => exact Or.inl rfl
  | success next => exact Or.inr ⟨next, rfl, rfl⟩

/-- Workspace and instruction revision are installed from the same successful
candidate, rather than from independently mutable fields. -/
theorem successful_refresh_binds_workspace_and_instructions
    (live next :
      Epoch Workspace OperationalRevision InstructionRevision
        CommitmentProjection View) :
    (promote live (.success next)).workspace = next.workspace ∧
      (promote live (.success next)).instructionRevision =
        next.instructionRevision := by
  exact ⟨rfl, rfl⟩

/-- A failed refresh cannot silently drop protected commitment context. -/
theorem failed_refresh_preserves_commitment_projection
    (live :
      Epoch Workspace OperationalRevision InstructionRevision
        CommitmentProjection View) :
    (promote live .failure).commitments = live.commitments := by
  rfl

/-- Inability to obtain a completed epoch preserves the last-known live
epoch.  `observed none` here means that no complete epoch was produced; source-
local deletion is handled before epoch construction. -/
def promoteObservation (live : EpochType) :
    SourceObservation EpochType → EpochType
  | .unavailable => live
  | .observed none => live
  | .observed (some next) => next

@[simp] theorem unavailable_epoch_stutters (live : EpochType) :
    promoteObservation live .unavailable = live := by
  rfl

@[simp] theorem incomplete_epoch_stutters (live : EpochType) :
    promoteObservation live (.observed none) = live := by
  rfl

@[simp] theorem completed_epoch_promotes (live next : EpochType) :
    promoteObservation live (.observed (some next)) = next := by
  rfl

/-- A context request carries the epoch as one value.  Consumers may project
coordinates, but cannot receive a workspace from one epoch and a view from
another through this constructor. -/
structure Request (EpochType Payload : Type*) where
  epoch : EpochType
  payload : Payload
deriving Repr, DecidableEq

def prepare (epoch : EpochType) (payload : Payload) : Request EpochType Payload :=
  ⟨epoch, payload⟩

@[simp] theorem prepared_request_uses_exact_epoch
    (epoch : EpochType) (payload : Payload) :
    (prepare epoch payload).epoch = epoch := by
  rfl

/-! ## Optimistic publication through the existing atomic snapshot boundary

An asynchronous refresh must validate the complete epoch it read, not just a
sequence number. The target is installed as one value at the next sequence.
`AtomicSnapshotTransaction` retains the publication occurrence on conflict;
this adapter adds no second transaction mechanism.
-/

section Publication

variable {Workspace OperationalRevision InstructionRevision
  CommitmentProjection View : Type*}

local notation "Context" => Epoch Workspace OperationalRevision InstructionRevision
  CommitmentProjection View

/-- The request's epoch is the captured parent; its payload is a complete
candidate. Sequence allocation belongs to the atomic publication boundary. -/
def publicationTarget (request : Request Context Context) : Context :=
  { request.payload with sequence := request.epoch.sequence + 1 }

def publicationSpec :
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Spec
      Nat Context Context (Request Context Context) where
  capturedRevision request := request.epoch.sequence
  capturedState request := request.epoch
  targetState := publicationTarget
  pendingWork request := [publicationTarget request]

def snapshot (epoch : Context) :
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Snapshot Nat Context :=
  ⟨epoch.sequence, epoch⟩

variable [DecidableEq Workspace] [DecidableEq OperationalRevision]
  [DecidableEq InstructionRevision] [DecidableEq CommitmentProjection]
  [DecidableEq View]

/-- Validate against both the live sequence and the complete live epoch. -/
def publicationDecision (live : Context) (request : Request Context Context) :=
  Mettapedia.GSLT.Core.AtomicSnapshotTransaction.attempt publicationSpec
    request (snapshot live) (live.sequence + 1) (by
      change live.sequence + 1 ≠ live.sequence
      omega)

def publish (live : Context) (request : Request Context Context) : Context :=
  (publicationDecision live request).physicalSnapshot.state

@[simp] theorem publish_current (live next : Context) :
    publish live (prepare live next) =
      { next with sequence := live.sequence + 1 } := by
  simp [publish, publicationDecision, publicationSpec, snapshot, prepare,
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.attempt,
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Decision.physicalSnapshot,
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.CommitReceipt.after,
    publicationTarget]

theorem publish_stale (live : Context) (request : Request Context Context)
    (stale : live ≠ request.epoch) : publish live request = live := by
  by_cases revision : live.sequence = request.epoch.sequence
  all_goals
  simp [publish, publicationDecision, publicationSpec, snapshot,
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.attempt,
    Mettapedia.GSLT.Core.AtomicSnapshotTransaction.Decision.physicalSnapshot,
    stale, revision]

/-- Neither the sequence comparison nor the state comparison can admit a
partially assembled target. -/
theorem publish_atomic (live : Context) (request : Request Context Context) :
    publish live request = live ∨
      publish live request = publicationTarget request := by
  by_cases current : live = request.epoch
  · subst live
    exact Or.inr (publish_current request.epoch request.payload)
  · exact Or.inl (publish_stale live request current)

theorem publication_invalidates_sibling
    (live next other : Context) :
    publish (publish live (prepare live next)) (prepare live other) =
      publish live (prepare live next) := by
  apply publish_stale
  intro same
  have sequenceSame := congrArg Epoch.sequence same
  simp only [publish_current] at sequenceSame
  change live.sequence + 1 = live.sequence at sequenceSame
  omega

/-- A consumer may retain an old request as history. Reuse at the live epoch
requires a new exact comparison. -/
def Request.Current (request : Request Context Payload) (live : Context) : Prop :=
  request.epoch = live

theorem old_consumer_request_is_not_current
    (live next : Context) (payload : Payload) :
    ¬ (prepare live payload).Current (publish live (prepare live next)) := by
  intro same
  change live = publish live (prepare live next) at same
  rw [publish_current] at same
  have sequenceSame := congrArg Epoch.sequence same
  change live.sequence = live.sequence + 1 at sequenceSame
  omega

end Publication

end Mettapedia.CognitiveArchitecture.Agent.ContextEpoch

#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.promotion_is_atomic
#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.successful_refresh_binds_workspace_and_instructions
#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.failed_refresh_preserves_commitment_projection
