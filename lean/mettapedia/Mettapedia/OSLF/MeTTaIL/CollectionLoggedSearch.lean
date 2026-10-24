import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.Machines.ResumableSearchRunner

/-!
# Append-only collection search

The plan machine's derived publication is not prefix-monotone.  This adapter
retains each matcher lane, remembers how much of that lane has already been
published, and appends only newly observed firings to a chronological log.
The resulting search satisfies the generic explorer's `Search.Lawful`
contract without changing collection matching or its receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch

open Syntax
open Mettapedia.Machines.ResumableSearchRunner

structure Lane where
  ordinal : Nat
  request : ScopedCollectionMachine.Request
  state : ScopedCollectionMachine.State
  spent : Nat
  consumed : Nat
  state_eq : state = ScopedCollectionMachine.resume request spent
    (ScopedCollectionMachine.start request)
  consumed_le : consumed ≤ (ScopedCollectionMachine.firings request state).length

def Lane.begin (entry : Nat × ScopedCollectionMachine.Request) : Lane :=
  { ordinal := entry.1, request := entry.2,
    state := ScopedCollectionMachine.start entry.2,
    spent := 0, consumed := 0,
    state_eq := (ScopedCollectionMachine.resume_zero _ _).symm,
    consumed_le := Nat.zero_le _ }

def tag (lane : Lane) (receipt : ScopedCollectionMachine.FiringReceipt) :
    CollectionPlanMachine.Firing := ⟨lane.ordinal, lane.request, receipt⟩

/-- Resume each retained allocation and drain its own publication suffix.
A cursor over the flattened list would miss an earlier allocation that
finishes after a later one. The retained wire cursor is distributed over the
previous per-allocation prefixes before any new results are appended. -/
def advanceJobs (request : ScopedCollectionMachine.Request) :
    Nat → ScopedCollectionMachine.State →
      ScopedCollectionMachine.State × List ScopedCollectionMachine.FiringReceipt
  | _, [] => ([], [])
  | consumed, job :: jobs =>
      let next := { job with state :=
        GeneralScopedMatchMachine.run request.machine 1 job.state }
      let previous := ScopedCollectionMachine.firings request [job]
      let later := advanceJobs request (consumed - previous.length) jobs
      (next :: later.1,
        (ScopedCollectionMachine.firings request [next]).drop
          (min consumed previous.length) ++ later.2)

theorem advanceJobs_state (request : ScopedCollectionMachine.Request)
    (consumed : Nat) (jobs : ScopedCollectionMachine.State) :
    (advanceJobs request consumed jobs).1 = ScopedCollectionMachine.resume request 1 jobs := by
  induction jobs generalizing consumed with
  | nil => rfl
  | cons job jobs ih => simp only [advanceJobs, ScopedCollectionMachine.resume,
      List.map_cons, ih]

theorem advanceJobs_fresh_mem (request : ScopedCollectionMachine.Request)
    (consumed : Nat) (jobs : ScopedCollectionMachine.State)
    {receipt : ScopedCollectionMachine.FiringReceipt}
    (member : receipt ∈ (advanceJobs request consumed jobs).2) :
    receipt ∈ ScopedCollectionMachine.firings request
      (ScopedCollectionMachine.resume request 1 jobs) := by
  induction jobs generalizing consumed with
  | nil => cases member
  | cons job jobs ih =>
      simp only [advanceJobs, List.mem_append] at member
      have split : ScopedCollectionMachine.firings request
          (ScopedCollectionMachine.resume request 1 (job :: jobs)) =
          ScopedCollectionMachine.firings request
            [{ job with state := GeneralScopedMatchMachine.run request.machine 1 job.state }] ++
          ScopedCollectionMachine.firings request
            (ScopedCollectionMachine.resume request 1 jobs) := by
        simp [ScopedCollectionMachine.firings, ScopedCollectionMachine.publication,
          ScopedCollectionMachine.resume, List.filterMap_append]
      rw [split, List.mem_append]
      exact member.elim (fun head => .inl (List.mem_of_mem_drop head))
        (fun tail => .inr (ih _ tail))

def advanceLane (lane : Lane) : Lane × List CollectionPlanMachine.Firing :=
  let advanced := advanceJobs lane.request lane.consumed lane.state
  let nextState := advanced.1
  let published := ScopedCollectionMachine.firings lane.request nextState
  let fresh := advanced.2.map (tag lane)
  let next : Lane :=
    { lane with
      state := nextState
      spent := lane.spent + 1
      consumed := published.length
      state_eq := by
        dsimp only [nextState, advanced]
        rw [advanceJobs_state, lane.state_eq, ← ScopedCollectionMachine.resume_add]
      consumed_le := Nat.le_refl _ }
  (next, fresh)

structure State where
  lanes : List Lane
  log : List CollectionPlanMachine.Firing

def begin (requests : List (Nat × ScopedCollectionMachine.Request)) : State :=
  ⟨requests.map Lane.begin, []⟩

def round (state : State) : State :=
  let advanced := state.lanes.map advanceLane
  { lanes := advanced.map Prod.fst,
    log := state.log ++ advanced.flatMap Prod.snd }

def resume : Nat → State → State
  | 0, state => state
  | fuel + 1, state => resume fuel (round state)

theorem resume_add (first extra : Nat) (state : State) :
    resume (first + extra) state = resume extra (resume first state) := by
  induction first generalizing state with
  | zero => simp [resume]
  | succ first ih => simpa only [Nat.succ_add, resume] using ih (round state)

theorem round_log_prefix (state : State) : state.log <+: (round state).log := by
  exact ⟨_, rfl⟩

theorem resume_log_prefix (fuel : Nat) (state : State) :
    state.log <+: (resume fuel state).log := by
  induction fuel generalizing state with
  | zero => exact ⟨[], by simp [resume]⟩
  | succ fuel ih =>
      exact (round_log_prefix state).trans (ih (round state))

def Valid (requests : List (Nat × ScopedCollectionMachine.Request))
    (firing : CollectionPlanMachine.Firing) : Prop :=
  (firing.ordinal, firing.request) ∈ requests ∧ firing.Valid

def Lane.From (requests : List (Nat × ScopedCollectionMachine.Request))
    (lane : Lane) : Prop := (lane.ordinal, lane.request) ∈ requests

def Invariant (requests : List (Nat × ScopedCollectionMachine.Request))
    (state : State) : Prop :=
  (∀ lane ∈ state.lanes, lane.From requests) ∧
  ∀ firing ∈ state.log, Valid requests firing

theorem begin_invariant (requests : List (Nat × ScopedCollectionMachine.Request)) :
    Invariant requests (begin requests) := by
  constructor
  · intro lane member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    simpa [Lane.From, Lane.begin] using present
  · intro firing member
    cases member

theorem advanceLane_origin {requests : List (Nat × ScopedCollectionMachine.Request)}
    {lane : Lane} (origin : lane.From requests) :
    (advanceLane lane).1.From requests := by
  exact origin

theorem advanceLane_fresh_sound {requests : List (Nat × ScopedCollectionMachine.Request)}
    {lane : Lane} (origin : lane.From requests) {firing : CollectionPlanMachine.Firing}
    (member : firing ∈ (advanceLane lane).2) : Valid requests firing := by
  unfold advanceLane at member
  dsimp only at member
  obtain ⟨receipt, fresh, rfl⟩ := List.mem_map.mp member
  have published : receipt ∈ ScopedCollectionMachine.firings lane.request
      (ScopedCollectionMachine.resume lane.request 1 lane.state) :=
    advanceJobs_fresh_mem lane.request lane.consumed lane.state fresh
  have stateEq : ScopedCollectionMachine.resume lane.request 1 lane.state =
      ScopedCollectionMachine.resume lane.request (lane.spent + 1)
        (ScopedCollectionMachine.start lane.request) := by
    rw [lane.state_eq, ← ScopedCollectionMachine.resume_add]
  refine ⟨origin, ?_⟩
  exact ScopedCollectionMachine.firings_sound lane.request (lane.spent + 1)
    (stateEq ▸ published)

theorem round_invariant {requests : List (Nat × ScopedCollectionMachine.Request)}
    {state : State} (holds : Invariant requests state) :
    Invariant requests (round state) := by
  constructor
  · intro lane member
    simp only [round, List.mem_map] at member
    obtain ⟨pair, ⟨original, present, rfl⟩, rfl⟩ := member
    exact advanceLane_origin (holds.1 original present)
  · intro firing member
    simp only [round, List.mem_append] at member
    rcases member with old | fresh
    · exact holds.2 firing old
    · obtain ⟨pair, paired, inside⟩ := List.mem_flatMap.mp fresh
      obtain ⟨lane, present, equal⟩ := List.mem_map.mp paired
      subst pair
      exact advanceLane_fresh_sound (holds.1 lane present) inside

theorem resume_invariant {requests : List (Nat × ScopedCollectionMachine.Request)}
    (fuel : Nat) {state : State} (holds : Invariant requests state) :
    Invariant requests (resume fuel state) := by
  induction fuel generalizing state with
  | zero => exact holds
  | succ fuel ih => exact ih (round_invariant holds)

/-- A finished matcher may still have firings behind its publication cursor.
Completion includes draining that cursor into the chronological log. -/
def Lane.complete (lane : Lane) : Bool :=
  ScopedCollectionMachine.complete lane.state &&
    lane.consumed == (ScopedCollectionMachine.firings lane.request lane.state).length

def complete (state : State) : Bool := state.lanes.all Lane.complete

structure Run where
  source : Pattern
  state : State

def requests (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) (source : Pattern) :=
  CollectionExecutionAdmission.requestsForSource plan certificate source

def run (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (work : Nat) : Run :=
  ⟨source, resume work (begin (requests plan certificate source))⟩

def resumeRun (_plan : GeneralExecutionAdmission.Plan)
    (_certificate : CollectionExecutionAdmission.Certificate _plan)
    (state : Run) (extra : Nat) : Run :=
  ⟨state.source, resume extra state.state⟩

def search (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) :
    Search Pattern Run CollectionPlanMachine.Firing where
  run := run plan certificate
  resume := resumeRun plan certificate
  publication state := state.state.log
  status state := if complete state.state then .complete else .pending
  target firing := CanonicalBags.canon firing.receipt.target
  Valid source firing := Valid (requests plan certificate source) firing

theorem search_lawful (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) :
    (search plan certificate).Lawful where
  resume_run source first extra := by
    change Run.mk source (resume extra (resume first (begin _))) =
      Run.mk source (resume (first + extra) (begin _))
    congr 1
    exact (resume_add first extra _).symm
  publication_prefix source first extra := by
    change (resume first (begin (requests plan certificate source))).log <+:
      (resume (first + extra) (begin (requests plan certificate source))).log
    rw [resume_add]
    exact resume_log_prefix extra _
  sound source work firing member := by
    change firing ∈ (resume work (begin (requests plan certificate source))).log at member
    exact (resume_invariant work (begin_invariant _)).2 firing member

#print axioms search_lawful

end Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
