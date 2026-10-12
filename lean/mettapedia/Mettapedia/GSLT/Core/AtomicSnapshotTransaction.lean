import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.Algebra.OccurrenceIdentity

/-!
# Policy-neutral atomic snapshot transactions

This module isolates the common transaction law beneath speculative
evaluation, optimizer trials, space overlays, and revision-scoped execution.
A proposal names the snapshot it was derived from, its exact target state, and
the work occurrences represented by the proposal.  A physical commit is
permitted only when both the live revision and the live state still match that
captured snapshot.

The result is deliberately small:

* a successful receipt atomically exposes the complete target at a fresh
  revision;
* a conflict exposes the live snapshot unchanged and retains all work as
  pending; and
* every accepted commit makes proposals derived from the old revision stale.

Retry, serial fallback, compatible merge, and rejection are policies over the
deferred constructor.  They are not built into this transaction boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AtomicSnapshotTransaction

open Mettapedia.GSLT.Core.ResourceAwareControl

universe uRevision uState uWork uProposal
universe vRevision vState vWork wRevision wState wWork

/-! ## Captured and live state -/

/-- A complete physical snapshot.  The state is retained alongside the
revision so a backend cannot silently rely on an unsound revision discipline. -/
structure Snapshot (Revision : Type uRevision) (State : Type uState) where
  revision : Revision
  state : State
deriving DecidableEq, Repr

/-- The semantic interpretation of a proposal.  Proposal evidence lives in
the proposal type; this record only states how the atomic layer reads its
captured revision, captured parent, complete target, and retained work. -/
structure Spec (Revision : Type uRevision) (State : Type uState)
    (Work : Type uWork) (Proposal : Type uProposal) where
  capturedRevision : Proposal → Revision
  capturedState : Proposal → State
  targetState : Proposal → State
  pendingWork : Proposal → List Work

def Spec.captured
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal) (proposal : Proposal) :
    Snapshot Revision State :=
  ⟨spec.capturedRevision proposal, spec.capturedState proposal⟩

/-- Exact optimistic validation.  Matching only the revision is insufficient:
the live state must also equal the captured parent. -/
structure Matches
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) : Prop where
  revision_eq : live.revision = spec.capturedRevision proposal
  state_eq : live.state = spec.capturedState proposal

theorem captured_matches
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal) (proposal : Proposal) :
    Matches spec proposal (spec.captured proposal) :=
  ⟨rfl, rfl⟩

/-! ## Atomic commit and exact deferral -/

/-- A successful atomic commit.  The semantic target is read directly from
the proposal, while the fresh revision is retained as an explicit receipt. -/
structure CommitReceipt
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) where
  current : Matches spec proposal live
  nextRevision : Revision
  advanced : nextRevision ≠ live.revision

def CommitReceipt.after
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}
    (receipt : CommitReceipt spec proposal live) : Snapshot Revision State :=
  ⟨receipt.nextRevision, spec.targetState proposal⟩

/-- The atomic boundary has exactly two semantic outcomes.  A conflict proof
does not choose what a later controller will do with the pending proposal. -/
inductive Decision
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State) where
  | committed (receipt : CommitReceipt spec proposal live)
  | deferred (conflict : ¬ Matches spec proposal live)

/-- The executable exact validator.  It accepts only equality of the complete
captured snapshot and otherwise returns the proof-relevant deferred branch. -/
def attempt
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    [DecidableEq Revision] [DecidableEq State]
    (spec : Spec Revision State Work Proposal)
    (proposal : Proposal) (live : Snapshot Revision State)
    (nextRevision : Revision) (advanced : nextRevision ≠ live.revision) :
    Decision spec proposal live :=
  if revisionMatches : live.revision = spec.capturedRevision proposal then
    if stateMatches : live.state = spec.capturedState proposal then
      .committed
        { current := ⟨revisionMatches, stateMatches⟩
          nextRevision := nextRevision
          advanced := advanced }
    else
      .deferred fun current => stateMatches current.state_eq
  else
    .deferred fun current => revisionMatches current.revision_eq

namespace Decision

variable
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}

/-- Atomicity: a commit exposes the complete proposal target, while deferral
returns the live snapshot exactly. -/
def physicalSnapshot : Decision spec proposal live → Snapshot Revision State
  | .committed receipt => receipt.after
  | .deferred _ => live

/-- Occurrence ledger for the complete proposal.  No work position can vanish
at the transaction boundary. -/
def ledger (decision : Decision spec proposal live) :
    FundingDecision.Ledger Work :=
  match decision with
  | .committed _ => ⟨(spec.pendingWork proposal : Multiset Work), 0⟩
  | .deferred _ => ⟨0, (spec.pendingWork proposal : Multiset Work)⟩

/-- The position-preserving form of the same all-or-nothing work receipt.
Candidate observers may lawfully forget order, but FIFO and age-sensitive
retry controllers must not reconstruct it from a multiset. -/
structure OrderedLedger (Work : Type uWork) where
  executed : List Work
  pending : List Work
deriving Repr

def orderedLedger (decision : Decision spec proposal live) :
    OrderedLedger Work :=
  match decision with
  | .committed _ => ⟨spec.pendingWork proposal, []⟩
  | .deferred _ => ⟨[], spec.pendingWork proposal⟩

/-- Forgetting position from the ordered receipt recovers exactly the existing
multiset receipt, coordinate by coordinate. -/
theorem orderedLedger_erases_to_ledger
    (decision : Decision spec proposal live) :
    (decision.orderedLedger.executed : Multiset Work) =
        decision.ledger.executed ∧
      (decision.orderedLedger.pending : Multiset Work) =
        decision.ledger.pending := by
  cases decision <;> exact ⟨rfl, rfl⟩

/-- Atomicity also accounts for the exact authored list: one side is complete
and the other is empty. -/
theorem orderedLedger_accounts
    (decision : Decision spec proposal live) :
    decision.orderedLedger.executed ++ decision.orderedLedger.pending =
      spec.pendingWork proposal := by
  cases decision <;> simp [orderedLedger]

theorem ledger_accounts (decision : Decision spec proposal live) :
    decision.ledger.executed + decision.ledger.pending =
      (spec.pendingWork proposal : Multiset Work) := by
  cases decision <;> simp [ledger]

@[simp] theorem committed_physical_snapshot
    (receipt : CommitReceipt spec proposal live) :
    physicalSnapshot (Decision.committed receipt) = receipt.after :=
  rfl

@[simp] theorem deferred_is_exact_rollback
    (conflict : ¬ Matches spec proposal live) :
    physicalSnapshot (Decision.deferred conflict) = live :=
  rfl

@[simp] theorem committed_executes_exact_work
    (receipt : CommitReceipt spec proposal live) :
    (Decision.committed receipt).ledger.executed =
      (spec.pendingWork proposal : Multiset Work) :=
  rfl

@[simp] theorem committed_executes_exact_ordered_work
    (receipt : CommitReceipt spec proposal live) :
    (Decision.committed receipt).orderedLedger.executed =
      spec.pendingWork proposal :=
  rfl

@[simp] theorem deferred_retains_exact_work
    (conflict : ¬ Matches spec proposal live) :
    (Decision.deferred conflict).ledger.pending =
      (spec.pendingWork proposal : Multiset Work) :=
  rfl

@[simp] theorem deferred_retains_exact_ordered_work
    (conflict : ¬ Matches spec proposal live) :
    (Decision.deferred conflict).orderedLedger.pending =
      spec.pendingWork proposal :=
  rfl

end Decision

namespace CommitReceipt

variable
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {spec : Spec Revision State Work Proposal}
    {proposal : Proposal} {live : Snapshot Revision State}

/-- A successful revision advance makes the same captured proposal stale. -/
theorem after_rejects_same_proposal
    (receipt : CommitReceipt spec proposal live) :
    ¬ Matches spec proposal receipt.after := by
  intro currentAfter
  apply receipt.advanced
  calc
    receipt.nextRevision = spec.capturedRevision proposal :=
      currentAfter.revision_eq
    _ = live.revision := receipt.current.revision_eq.symm

/-- A sibling derived from the same captured revision is also stale after one
commit.  It may be retried only by producing a new proposal or by an authored
merge/fallback policy that earns a different receipt. -/
theorem after_rejects_same_revision_sibling
    (receipt : CommitReceipt spec proposal live)
    {sibling : Proposal}
    (sameRevision :
      spec.capturedRevision sibling = spec.capturedRevision proposal) :
    ¬ Matches spec sibling receipt.after := by
  intro currentAfter
  apply receipt.advanced
  calc
    receipt.nextRevision = spec.capturedRevision sibling :=
      currentAfter.revision_eq
    _ = spec.capturedRevision proposal := sameRevision
    _ = live.revision := receipt.current.revision_eq.symm

end CommitReceipt

/-! ## Faithful transport to another owned snapshot -/

/-- Transport the revision and the complete state separately.  Changing an
owner coordinate must not erase either the revision or the state comparison. -/
def Snapshot.map
    {Revision : Type uRevision} {State : Type uState}
    {NextRevision : Type vRevision} {NextState : Type vState}
    (revision : Revision → NextRevision) (state : State → NextState)
    (snapshot : Snapshot Revision State) : Snapshot NextRevision NextState :=
  ⟨revision snapshot.revision, state snapshot.state⟩

@[simp] theorem Snapshot.map_id
    {Revision : Type uRevision} {State : Type uState}
    (snapshot : Snapshot Revision State) : snapshot.map id id = snapshot := by
  cases snapshot
  rfl

theorem Snapshot.map_comp
    {Revision : Type uRevision} {State : Type uState}
    {NextRevision : Type vRevision} {NextState : Type vState}
    {FinalRevision : Type wRevision} {FinalState : Type wState}
    (revision : Revision → NextRevision) (state : State → NextState)
    (nextRevision : NextRevision → FinalRevision) (nextState : NextState → FinalState)
    (snapshot : Snapshot Revision State) :
    (snapshot.map revision state).map nextRevision nextState =
      snapshot.map (nextRevision ∘ revision) (nextState ∘ state) := rfl

/-- A proposal keeps its identity while all its snapshot fields and ordered
work occurrences are transported.  This does not recompute a proposal from
its target or rebuild its pending list from a bag. -/
def Spec.map
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {NextRevision : Type vRevision} {NextState : Type vState} {NextWork : Type vWork}
    (spec : Spec Revision State Work Proposal)
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork) : Spec NextRevision NextState NextWork Proposal where
  capturedRevision proposal := revision (spec.capturedRevision proposal)
  capturedState proposal := state (spec.capturedState proposal)
  targetState proposal := state (spec.targetState proposal)
  pendingWork proposal := (spec.pendingWork proposal).map work

@[simp] theorem Spec.map_captured
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {NextRevision : Type vRevision} {NextState : Type vState} {NextWork : Type vWork}
    (spec : Spec Revision State Work Proposal)
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork) (proposal : Proposal) :
    (spec.map revision state work).captured proposal =
      (spec.captured proposal).map revision state := rfl

theorem Spec.map_comp
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {NextRevision : Type vRevision} {NextState : Type vState} {NextWork : Type vWork}
    {FinalRevision : Type wRevision} {FinalState : Type wState} {FinalWork : Type wWork}
    (spec : Spec Revision State Work Proposal)
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork) (nextRevision : NextRevision → FinalRevision)
    (nextState : NextState → FinalState) (nextWork : NextWork → FinalWork) :
    (spec.map revision state work).map nextRevision nextState nextWork =
      spec.map (nextRevision ∘ revision) (nextState ∘ state) (nextWork ∘ work) := by
  simp only [Spec.map, List.map_map, Function.comp_def]

namespace IdentityTransport

variable
    {Revision : Type uRevision} {State : Type uState}
    {Work : Type uWork} {Proposal : Type uProposal}
    {NextRevision : Type vRevision} {NextState : Type vState} {NextWork : Type vWork}

/-- Equality of both captured fields is preserved by any field maps. -/
theorem matchesMap
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} (current : Matches spec proposal live) :
    Matches (spec.map revision state work) proposal (live.map revision state) :=
  ⟨congrArg revision current.revision_eq, congrArg state current.state_eq⟩

/-- Reflecting a successful validation needs faithful maps of both fields.
An owner transport that merges states or revisions can turn a conflict into
a spurious commit. -/
theorem matches_map_iff
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    (spec : Spec Revision State Work Proposal) (proposal : Proposal)
    (live : Snapshot Revision State) :
    Matches (spec.map revision state work) proposal (live.map revision state) ↔
      Matches spec proposal live := by
  constructor
  · intro current
    exact ⟨revisionFaithful current.revision_eq, stateFaithful current.state_eq⟩
  · exact matchesMap revision state work

def receiptMap
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork) (revisionFaithful : Function.Injective revision)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} (receipt : CommitReceipt spec proposal live) :
    CommitReceipt (spec.map revision state work) proposal (live.map revision state) where
  current := matchesMap revision state work receipt.current
  nextRevision := revision receipt.nextRevision
  advanced equality := receipt.advanced (revisionFaithful equality)

@[simp] theorem receiptMap_after
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork) (revisionFaithful : Function.Injective revision)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} (receipt : CommitReceipt spec proposal live) :
    (receiptMap revision state work revisionFaithful receipt).after =
      receipt.after.map revision state := rfl

/-- Transport successful and refused decisions; refusals remain proofs of
the same complete-state mismatch rather than being retried during copying. -/
def decisionMap
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} : Decision spec proposal live →
    Decision (spec.map revision state work) proposal (live.map revision state)
  | .committed receipt => .committed (receiptMap revision state work revisionFaithful receipt)
  | .deferred conflict => .deferred fun current =>
      conflict ((matches_map_iff revision state work revisionFaithful stateFaithful
        spec proposal live).mp current)

/-- The independently executable exact validator commutes with faithful
transport.  In particular, copying cannot refresh a stale captured revision
or make an unexplained state change disappear. -/
theorem attempt_map
    [DecidableEq Revision] [DecidableEq State]
    [DecidableEq NextRevision] [DecidableEq NextState]
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    (spec : Spec Revision State Work Proposal) (proposal : Proposal)
    (live : Snapshot Revision State) (nextRevision : Revision)
    (advanced : nextRevision ≠ live.revision) :
    attempt (spec.map revision state work) proposal (live.map revision state)
        (revision nextRevision) (fun equality => advanced (revisionFaithful equality)) =
      decisionMap revision state work revisionFaithful stateFaithful
        (attempt spec proposal live nextRevision advanced) := by
  by_cases sameRevision : live.revision = spec.capturedRevision proposal
  · by_cases sameState : live.state = spec.capturedState proposal
    · simp [attempt, Spec.map, Snapshot.map, sameRevision,
        sameState, decisionMap, receiptMap]
    · have mappedState : state live.state ≠ state (spec.capturedState proposal) :=
        fun equality => sameState (stateFaithful equality)
      simp [attempt, Spec.map, Snapshot.map, sameRevision,
        sameState, mappedState, decisionMap]
  · have mappedRevision : revision live.revision ≠ revision (spec.capturedRevision proposal) :=
      fun equality => sameRevision (revisionFaithful equality)
    simp [attempt, Spec.map, Snapshot.map, sameRevision, mappedRevision, decisionMap]

theorem decisionMap_physicalSnapshot
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} (decision : Decision spec proposal live) :
    (decisionMap revision state work revisionFaithful stateFaithful decision).physicalSnapshot =
      decision.physicalSnapshot.map revision state := by
  cases decision <;> rfl

/-- Keep the complete ordered occurrence word on whichever side of the
atomic boundary the original decision placed it. -/
theorem decisionMap_orderedLedger
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    {spec : Spec Revision State Work Proposal} {proposal : Proposal}
    {live : Snapshot Revision State} (decision : Decision spec proposal live) :
    (decisionMap revision state work revisionFaithful stateFaithful decision).orderedLedger.executed =
        decision.orderedLedger.executed.map work ∧
      (decisionMap revision state work revisionFaithful stateFaithful decision).orderedLedger.pending =
        decision.orderedLedger.pending.map work := by
  cases decision <;> exact ⟨rfl, rfl⟩

/-- The transported validator's whole physical readout follows from its
decision comparison, rather than validating a second reconstructed copy. -/
theorem attempt_map_physicalSnapshot
    [DecidableEq Revision] [DecidableEq State]
    [DecidableEq NextRevision] [DecidableEq NextState]
    (revision : Revision → NextRevision) (state : State → NextState)
    (work : Work → NextWork)
    (revisionFaithful : Function.Injective revision) (stateFaithful : Function.Injective state)
    (spec : Spec Revision State Work Proposal) (proposal : Proposal)
    (live : Snapshot Revision State) (nextRevision : Revision)
    (advanced : nextRevision ≠ live.revision) :
    (attempt (spec.map revision state work) proposal (live.map revision state)
        (revision nextRevision) (fun equality => advanced (revisionFaithful equality))).physicalSnapshot =
      (attempt spec proposal live nextRevision advanced).physicalSnapshot.map revision state := by
  rw [attempt_map]
  exact decisionMap_physicalSnapshot revision state work revisionFaithful stateFaithful _

open Mettapedia.Algebra.OccurrenceIdentity in
/-- Replacing only the current revision by a freshly issued representative
preserves and reflects exact validation on held source revisions. The state
comparison remains complete; copying does not resolve a stale proposal. -/
theorem matches_current_relocation_iff
    (bound current replacement : Nat) (fresh : bound ≤ replacement)
    (spec : Spec (Fin bound) State Work Proposal) (proposal : Proposal)
    (live : Snapshot (Fin bound) State) :
    let revision := fun identity : Fin bound =>
      CurrentRelocation.move current replacement identity.val
    Matches (spec.map revision id id) proposal (live.map revision id) ↔
      Matches spec proposal live :=
  matches_map_iff _ id id (CurrentRelocation.injective_on_prefix bound current replacement fresh)
    (fun _ _ equal => equal) spec proposal live

open Mettapedia.Algebra.OccurrenceIdentity in
/-- The actual exact validator, including its refused result and retained
work, commutes with current-identity relocation. Every compared source
revision is held below the issuance bound; this is not a global renaming. -/
theorem attempt_current_relocation [DecidableEq State]
    (bound current replacement : Nat) (fresh : bound ≤ replacement)
    (spec : Spec (Fin bound) State Work Proposal) (proposal : Proposal)
    (live : Snapshot (Fin bound) State) (nextRevision : Fin bound)
    (advanced : nextRevision ≠ live.revision) :
    let revision := fun identity : Fin bound =>
      CurrentRelocation.move current replacement identity.val
    let faithful := CurrentRelocation.injective_on_prefix bound current replacement fresh
    attempt (spec.map revision id id) proposal (live.map revision id)
        (revision nextRevision) (fun equality => advanced (faithful equality)) =
      decisionMap revision id id faithful (fun _ _ equal => equal)
        (attempt spec proposal live nextRevision advanced) :=
  attempt_map _ id id (CurrentRelocation.injective_on_prefix bound current replacement fresh)
    (fun _ _ equal => equal) spec proposal live nextRevision advanced

end IdentityTransport

/-! ## Positive and negative controls -/

namespace Canary

inductive Proposal where
  | left
  | right
deriving DecidableEq, Repr

def spec : Spec Nat Nat Proposal Proposal where
  capturedRevision _ := 7
  capturedState _ := 10
  targetState
    | .left => 11
    | .right => 12
  pendingWork proposal := [proposal]

def live : Snapshot Nat Nat := ⟨7, 10⟩

def leftReceipt : CommitReceipt spec .left live where
  current := ⟨rfl, rfl⟩
  nextRevision := 8
  advanced := by decide

def committedLeft : Decision spec .left live :=
  .committed leftReceipt

/-- Positive control: an exact current proposal commits its complete target at
the fresh revision and accounts for its occurrence once. -/
theorem current_commit_is_atomic :
    committedLeft.physicalSnapshot = ⟨8, 11⟩ ∧
      committedLeft.ledger.executed = {.left} ∧
      committedLeft.ledger.pending = 0 := by
  decide

def staleLive : Snapshot Nat Nat := ⟨8, 10⟩

def staleDecision : Decision spec .left staleLive :=
  attempt spec .left staleLive 9 (by decide)

/-- A changed revision rolls back exactly even when the state payload still
equals the captured state. -/
theorem changed_revision_is_exact_rollback :
    staleDecision.physicalSnapshot = staleLive ∧
      staleDecision.ledger.executed = 0 ∧
      staleDecision.ledger.pending = {.left} := by
  decide

def changedStateLive : Snapshot Nat Nat := ⟨7, 99⟩

def changedStateDecision : Decision spec .left changedStateLive :=
  attempt spec .left changedStateLive 8 (by decide)

/-- Matching revision alone is not enough: an unexplained state change also
forces exact rollback and preserves the work occurrence. -/
theorem changed_state_is_exact_rollback :
    changedStateDecision.physicalSnapshot = changedStateLive ∧
      changedStateDecision.ledger.executed = 0 ∧
      changedStateDecision.ledger.pending = {.left} := by
  decide

/-- Once the left proposal commits, the right proposal captured from the same
snapshot cannot race into the successor without revalidation. -/
theorem committed_revision_rejects_sibling :
    ¬ Matches spec .right leftReceipt.after :=
  leftReceipt.after_rejects_same_revision_sibling rfl

/-- Multiset accounting preserves multiplicity but cannot reconstruct authored
retry order; the ordered ledger therefore carries genuine extra information. -/
theorem bag_receipt_does_not_recover_authored_order :
    ([Proposal.left, Proposal.right] : Multiset Proposal) =
        ([Proposal.right, Proposal.left] : Multiset Proposal) ∧
      ([Proposal.left, Proposal.right] : List Proposal) ≠
        [Proposal.right, Proposal.left] := by
  decide

/-- A nontrivial owner coordinate retains the original accepted target and
the ordered executed occurrence. -/
theorem private_owner_preserves_accepted_target :
    let moved := spec.map (fun revision => (41, revision))
      (fun state => (41, state)) (fun work => (41, work))
    let decision := attempt moved .left ⟨(41, 7), (41, 10)⟩ (41, 8) (by decide)
    decision.physicalSnapshot = ⟨(41, 8), (41, 11)⟩ ∧
      decision.orderedLedger.executed = [(41, .left)] ∧
      decision.orderedLedger.pending = [] := by
  decide

/-- Copying the same owner coordinate does not repair a stale original
revision, and preserves the exact pending occurrence. -/
theorem private_owner_preserves_stale_revision :
    let moved := spec.map (fun revision => (41, revision))
      (fun state => (41, state)) (fun work => (41, work))
    let decision := attempt moved .left ⟨(41, 8), (41, 10)⟩ (41, 9) (by decide)
    decision.physicalSnapshot = ⟨(41, 8), (41, 10)⟩ ∧
      decision.orderedLedger.executed = [] ∧
      decision.orderedLedger.pending = [(41, .left)] := by
  decide

/-- Complete-state transport detects a changed payload even when revision
comparison succeeds. -/
theorem private_owner_preserves_changed_state :
    let moved := spec.map (fun revision => (41, revision))
      (fun state => (41, state)) (fun work => (41, work))
    let decision := attempt moved .left ⟨(41, 7), (41, 99)⟩ (41, 8) (by decide)
    decision.physicalSnapshot = ⟨(41, 7), (41, 99)⟩ ∧
      decision.orderedLedger.pending = [(41, .left)] := by
  decide

open Mettapedia.Algebra.OccurrenceIdentity in
/-- A current proposal survives copying to a fresh current representative,
then commits at a newly advanced destination revision. -/
theorem current_relocation_preserves_commit :
    let moved := spec.map (CurrentRelocation.move 7 20) id id
    let decision := attempt moved .left ⟨20, 10⟩ 21 (by decide)
    decision.physicalSnapshot = ⟨21, 11⟩ ∧
      decision.orderedLedger.executed = [.left] ∧
      decision.orderedLedger.pending = [] := by
  decide

open Mettapedia.Algebra.OccurrenceIdentity in
/-- The same copy operation keeps a historical captured revision stale,
leaving the copied live state and pending work unchanged. -/
theorem current_relocation_retains_stale_proposal :
    let moved := spec.map (CurrentRelocation.move 8 20) id id
    let decision := attempt moved .left ⟨20, 10⟩ 21 (by decide)
    decision.physicalSnapshot = ⟨20, 10⟩ ∧
      decision.orderedLedger.executed = [] ∧
      decision.orderedLedger.pending = [.left] := by
  decide

open Mettapedia.Algebra.OccurrenceIdentity in
/-- Reusing an occupied destination rather than issuing a fresh one turns
the refused stale proposal into a spurious accepted transaction. -/
theorem occupied_relocation_invents_commit :
    let moved := spec.map (CurrentRelocation.move 8 7) id id
    let decision := attempt moved .left ⟨7, 10⟩ 9 (by decide)
    decision.physicalSnapshot = ⟨9, 11⟩ ∧
      decision.orderedLedger.executed = [.left] ∧
      staleDecision.orderedLedger.pending = [.left] := by
  decide

/-- Keeping only a display name for the state invents a successful commit
where the original validator refused an unexplained state change. -/
theorem state_erasure_invents_commit :
    let erased := spec.map id (fun _ => "world") id
    let decision := attempt erased .left ⟨7, "world"⟩ 8 (by decide)
    decision.orderedLedger.executed = [.left] ∧
      changedStateDecision.orderedLedger.pending = [.left] ∧
      changedStateDecision.orderedLedger.executed = [] := by
  decide

/-- Merging old revisions while retaining a different successor similarly
authorizes a stale proposal. -/
theorem revision_erasure_invents_commit :
    let revision := fun value : Nat => if value < 9 then 0 else value
    let erased := spec.map revision id id
    let decision := attempt erased .left ⟨0, 10⟩ 9 (by decide)
    decision.orderedLedger.executed = [.left] ∧
      staleDecision.orderedLedger.pending = [.left] ∧
      staleDecision.orderedLedger.executed = [] := by
  decide

end Canary

#print axioms captured_matches
#print axioms Decision.ledger_accounts
#print axioms Decision.orderedLedger_erases_to_ledger
#print axioms Decision.orderedLedger_accounts
#print axioms Decision.deferred_is_exact_rollback
#print axioms CommitReceipt.after_rejects_same_proposal
#print axioms CommitReceipt.after_rejects_same_revision_sibling
#print axioms Canary.current_commit_is_atomic
#print axioms Canary.changed_revision_is_exact_rollback
#print axioms Canary.changed_state_is_exact_rollback
#print axioms Canary.committed_revision_rejects_sibling
#print axioms Canary.bag_receipt_does_not_recover_authored_order
#print axioms IdentityTransport.matches_map_iff
#print axioms IdentityTransport.attempt_map
#print axioms IdentityTransport.decisionMap_physicalSnapshot
#print axioms IdentityTransport.decisionMap_orderedLedger
#print axioms IdentityTransport.attempt_map_physicalSnapshot
#print axioms IdentityTransport.matches_current_relocation_iff
#print axioms IdentityTransport.attempt_current_relocation
#print axioms Canary.private_owner_preserves_accepted_target
#print axioms Canary.private_owner_preserves_stale_revision
#print axioms Canary.private_owner_preserves_changed_state
#print axioms Canary.current_relocation_preserves_commit
#print axioms Canary.current_relocation_retains_stale_proposal
#print axioms Canary.occupied_relocation_invents_commit
#print axioms Canary.state_erasure_invents_commit
#print axioms Canary.revision_erasure_invents_commit

end Mettapedia.GSLT.Core.AtomicSnapshotTransaction
