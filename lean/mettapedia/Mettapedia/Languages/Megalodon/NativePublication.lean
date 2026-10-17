import Mettapedia.Languages.Megalodon.NativeSession
import Mettapedia.Languages.Megalodon.NativeAdmission
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# Atomic publication of a checked native theorem

The theory update and public result are one target state of the shared snapshot
transaction. Checking prepares that target without changing the live state.
The host reserves all storage before committing and checks current permission
at commitment. Refusal, resource failure, and snapshot conflict retain the
entire live state. The reservation argument models the host boundary; these
theorems do not verify an allocator, a native CAS, or capability enforcement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativePublication
open MathdataKernel
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction

structure State where
  environment : Environment
  publications : List (Name × Tm)
  deriving DecidableEq, Repr

abbrev World := Snapshot Nat State

structure Proposal where
  private mk ::
  captured : World
  name : Name
  theorem_ : NativeSession.Theorem captured.state.environment
  fresh : captured.state.environment.lookupKnown? name = none

def prepare (captured : World) (name : Name)
    (theorem_ : NativeSession.Theorem captured.state.environment) : Option Proposal :=
  if fresh : captured.state.environment.lookupKnown? name = none then
    some ⟨captured, name, theorem_, fresh⟩ else none

def target (proposal : Proposal) : State :=
  ⟨NativeAdmission.addKnown proposal.captured.state.environment proposal.name proposal.theorem_.proposition,
    proposal.captured.state.publications ++ [(proposal.name, proposal.theorem_.proposition)]⟩

def spec : Spec Nat State (Name × Tm) Proposal where
  capturedRevision proposal := proposal.captured.revision
  capturedState proposal := proposal.captured.state
  targetState := target
  pendingWork proposal := [(proposal.name, proposal.theorem_.proposition)]

/-- Publication extends the original selected environment by a proved theorem,
not by an extra import axiom or a claim embedded in the display text. -/
theorem target_admitted (proposal : Proposal) (authority : NativeAdmission.Authority) :
    ∃ fuel proof, NativeAdmission.Admits authority fuel proposal.captured.state.environment
      (.theorem_ proposal.name proposal.theorem_.proposition proof) (target proposal).environment := by
  obtain ⟨fuel, formed, proof, accepted⟩ := proposal.theorem_.valid
  exact ⟨fuel, proof, .theorem_ proposal.fresh formed accepted⟩

inductive Status where
  | published | resourceFailure | denied | conflict
  deriving DecidableEq, Repr

structure Result where
  status : Status
  world : World
  deriving DecidableEq, Repr

/-- `storageReady` is supplied by the host after reserving every owned result
and registry slot. It is not a user-visible flag or a proof of theoremhood. -/
def commit (proposal : Proposal) (live : World) (storageReady permitted : Bool) : Result :=
  if !storageReady then ⟨.resourceFailure, live⟩ else
    if !permitted then ⟨.denied, live⟩ else
      match attempt spec proposal live (live.revision + 1) (by omega) with
      | .committed receipt => ⟨.published, receipt.after⟩
      | .deferred _ => ⟨.conflict, live⟩

theorem no_storage_no_mutation (proposal : Proposal) (live : World) (permitted : Bool) :
    commit proposal live false permitted = ⟨.resourceFailure, live⟩ := rfl

theorem current_permission_required (proposal : Proposal) (live : World) :
    commit proposal live true false = ⟨.denied, live⟩ := rfl

theorem commit_exact (proposal : Proposal) (live : World) :
    commit proposal live true true =
      if live = proposal.captured then
        ⟨.published, ⟨live.revision + 1, target proposal⟩⟩ else ⟨.conflict, live⟩ := by
  rcases live with ⟨revision, state⟩
  by_cases revisions : revision = proposal.captured.revision <;>
    by_cases states : state = proposal.captured.state <;>
      simp [commit, attempt, spec, revisions, states, Snapshot.mk.injEq, CommitReceipt.after]
  all_goals
    intro equal
    have revisionEqual := congrArg Snapshot.revision equal
    have stateEqual := congrArg Snapshot.state equal
    simp_all

theorem failed_commit_unchanged (proposal : Proposal) (live : World) (storageReady permitted : Bool)
    (failed : (commit proposal live storageReady permitted).status ≠ .published) :
    (commit proposal live storageReady permitted).world = live := by
  cases storageReady <;> cases permitted
  all_goals try rfl
  rw [commit_exact] at failed ⊢
  by_cases same : live = proposal.captured <;> simp_all

theorem success_updates_both (proposal : Proposal) (live : World)
    (success : (commit proposal live true true).status = .published) :
    (commit proposal live true true).world.state.environment =
      NativeAdmission.addKnown live.state.environment proposal.name proposal.theorem_.proposition ∧
    (commit proposal live true true).world.state.publications =
      live.state.publications ++ [(proposal.name, proposal.theorem_.proposition)] := by
  rw [commit_exact] at success ⊢
  by_cases same : live = proposal.captured <;> simp_all [target]

theorem stale_proposal_conflicts (proposal : Proposal) (live : World)
    (changed : live ≠ proposal.captured) : commit proposal live true true = ⟨.conflict, live⟩ := by
  rw [commit_exact, if_neg changed]

theorem double_commit_refused (proposal : Proposal) :
    let first := commit proposal proposal.captured true true
    commit proposal first.world true true = ⟨.conflict, first.world⟩ := by
  simp only [commit_exact, ↓reduceIte]
  have different : (⟨proposal.captured.revision + 1, target proposal⟩ : World) ≠ proposal.captured := by
    intro same
    have revisions := congrArg Snapshot.revision same
    change proposal.captured.revision + 1 = proposal.captured.revision at revisions
    omega
  simp [different]

end Mettapedia.Languages.Megalodon.NativePublication
