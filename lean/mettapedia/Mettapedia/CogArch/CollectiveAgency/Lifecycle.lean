import Mettapedia.CogArch.CollectiveAgency.Memory
import Mettapedia.CogArch.Agent.GoalCommitment
import Mathlib.Data.Fintype.Pi

/-!
# Voluntary coalitions with persistent commitments

Formation requires each participant's consent. Subsequent collective decisions
use member majority, but a vote cannot fabricate individual consent, erase a
commitment, or grant a resource the issuer does not own. Proposal revision and
episode generation are separate scopes. Dissolution retains reports and
commitments while expiring membership and executable grants.

Immediate exit and commitment-bound release are different constitutions.
Neither prevents declining new work or stopping locally. Ordered withdrawal
records release; it does not notify partitioned replicas instantaneously.
Handover needs an offer by the responsible agent and acceptance by its successor.

These are mathematical interpretations of voluntary, temporary association,
not claims that the motivating essays supply a formal protocol:
https://theanarchistlibrary.org/library/hakim-bey-immediatism
https://theanarchistlibrary.org/library/hakim-bey-the-periodic-autonomous-zone
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.CollectiveAgency.Lifecycle

open Mettapedia.CogArch.Agent.GoalCommitment

inductive ExitProfile where
  | immediate
  | commitmentBound
  deriving DecidableEq, Repr

inductive Intent (A : Type*) where
  | form (participants : Finset A)
  | admit (participant : A)
  | dissolve
  deriving DecidableEq

inductive Command (A Task Resource Fact : Type*) where
  | propose (intent : Intent A)
  | consent
  | approve
  | form (participants : Finset A)
  | admit (participant : A)
  | contribute (source : Nat) (fact : Fact)
  | accept (task : Task)
  | refuse (task : Task)
  | discharge (task : Task) (witness : DropWitness Nat)
  | offer (task : Task) (successor : A)
  | takeOver (task : Task) (previous : A)
  | grant (resource : Resource) (recipient : A)
  | transfer (resource : Resource) (recipient : A)
  | withdraw
  | stop
  | dissolve
  deriving DecidableEq

structure Body (A Task Resource Fact : Type*) where
  generation : Nat
  revision : Nat
  live : Bool
  intent : Intent A
  consents : Finset A
  approvals : Finset A
  members : Finset A
  stopped : Finset A
  owner : Resource → A
  grants : Resource → Option (A × Nat)
  knowledge : Memory.Store (A × Nat) Fact
  responsible : Task → Option A
  commitments : Task → Status Nat
  offers : Finset (Task × A × A)

variable {A Task Resource Fact : Type*}
  [DecidableEq A] [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact]

def initial (owner : Resource → A) : Body A Task Resource Fact :=
  ⟨0, 0, false, .form ∅, ∅, ∅, ∅, ∅, owner, fun _ => none, ∅,
    fun _ => none, fun _ => .inactive, ∅⟩

def Majority (s : Body A Task Resource Fact) : Prop :=
  s.members.card < 2 * (s.approvals ∩ s.members).card

instance (s : Body A Task Resource Fact) : Decidable (Majority s) := by
  unfold Majority
  infer_instance

def ConsentsTo (intent : Intent A) (actor : A) : Prop :=
  match intent with
  | .form participants => actor ∈ participants
  | .admit target => actor = target
  | .dissolve => False

def Active (s : Body A Task Resource Fact) (actor : A) : Prop :=
  s.live = true ∧ actor ∈ s.members ∧ actor ∉ s.stopped

def NoBlocking (s : Body A Task Resource Fact) (actor : A) : Prop :=
  ∀ task, s.responsible task = some actor → s.commitments task ≠ .active

def MayRelease (profile : ExitProfile) (s : Body A Task Resource Fact) (actor : A) : Prop :=
  match profile with
  | .immediate => True
  | .commitmentBound => NoBlocking s actor

instance [Fintype Task] (profile : ExitProfile) (s : Body A Task Resource Fact) (actor : A) :
    Decidable (MayRelease profile s actor) := by
  cases profile <;> unfold MayRelease NoBlocking <;> infer_instance

def Allowed (profile : ExitProfile) (s : Body A Task Resource Fact) (actor : A) :
    Command A Task Resource Fact → Prop
  | .propose (.form _) => s.live = false
  | .propose _ => Active s actor
  | .consent => ConsentsTo s.intent actor
  | .approve => Active s actor
  | .form participants => s.live = false ∧ s.intent = .form participants ∧
      participants.Nonempty ∧ participants ⊆ s.consents ∧ actor ∈ participants
  | .admit target => Active s actor ∧ s.intent = .admit target ∧ Majority s ∧ target ∈ s.consents
  | .contribute _ _ => Active s actor
  | .accept task => Active s actor ∧ s.commitments task ≠ .active
  | .refuse _ => True
  | .discharge task _ => s.responsible task = some actor ∧ s.commitments task = .active
  | .offer task successor => s.responsible task = some actor ∧ s.commitments task = .active ∧
      Active s successor
  | .takeOver task previous => Active s actor ∧ (task, previous, actor) ∈ s.offers ∧
      s.responsible task = some previous ∧ s.commitments task = .active
  | .grant resource recipient => Active s actor ∧ s.owner resource = actor ∧
      s.grants resource = none ∧ recipient ∈ s.members
  | .transfer resource recipient => Active s actor ∧
      s.grants resource = some (actor, s.generation) ∧ recipient ∈ s.members
  | .withdraw => actor ∈ s.members ∧ MayRelease profile s actor
  | .stop => True
  | .dissolve => Active s actor ∧ s.intent = .dissolve ∧ Majority s ∧
      ∀ member ∈ s.members, MayRelease profile s member

instance (intent : Intent A) (actor : A) : Decidable (ConsentsTo intent actor) := by
  cases intent <;> unfold ConsentsTo <;> infer_instance

instance [Fintype Task] (profile : ExitProfile) (s : Body A Task Resource Fact)
    (actor : A) (command : Command A Task Resource Fact) : Decidable (Allowed profile s actor command) := by
  cases command with
  | propose intent => cases intent <;> unfold Allowed Active <;> infer_instance
  | withdraw => cases profile <;> unfold Allowed MayRelease NoBlocking <;> infer_instance
  | _ => unfold Allowed Active Majority; infer_instance

/-- Closing an episode expires authority, not memory, resource ownership or
outstanding obligations. It also handles departure of the final member. -/
def closeEpisode (s : Body A Task Resource Fact) : Body A Task Resource Fact :=
  { s with
    generation := s.generation + 1
    revision := 0
    live := false
    intent := .form ∅
    members := ∅
    consents := ∅
    approvals := ∅
    offers := ∅
    grants := fun _ => none }

/-- Command effects contain no admission decisions. -/
def update (s : Body A Task Resource Fact) (actor : A) :
    Command A Task Resource Fact → Body A Task Resource Fact
  | .propose intent => { s with
      intent := intent
      revision := s.revision + 1
      consents := ∅
      approvals := ∅ }
  | .consent => { s with
      consents := insert actor s.consents
      stopped := s.stopped.erase actor }
  | .approve => { s with approvals := insert actor s.approvals }
  | .form participants => { s with live := true, members := participants }
  | .admit target => { s with members := insert target s.members, approvals := ∅ }
  | .contribute source fact => { s with knowledge := Memory.report s.knowledge (actor, source) fact }
  | .accept task => { s with
      responsible := Function.update s.responsible task (some actor)
      commitments := Function.update s.commitments task .active
      offers := s.offers.filter (fun offer => offer.1 ≠ task) }
  | .refuse _ => s
  | .discharge task witness => { s with
      commitments := Function.update s.commitments task
        (Agent.GoalCommitment.step (s.commitments task) (.discharge witness))
      offers := s.offers.filter (fun offer => offer.1 ≠ task) }
  | .offer task successor => { s with offers := insert (task, actor, successor) s.offers }
  | .takeOver task _previous => { s with
      responsible := Function.update s.responsible task (some actor)
      offers := s.offers.filter (fun offer => offer.1 ≠ task) }
  | .grant resource recipient | .transfer resource recipient =>
      { s with grants := Function.update s.grants resource (some (recipient, s.generation)) }
  | .withdraw =>
      let remaining := { s with
        members := s.members.erase actor
        consents := s.consents.erase actor
        approvals := s.approvals.erase actor
        grants := fun resource => if (s.grants resource).map Prod.fst = some actor
          then none else s.grants resource }
      if remaining.members = ∅ then closeEpisode remaining else remaining
  | .stop => { s with stopped := insert actor s.stopped }
  | .dissolve => closeEpisode s

inductive Outcome where
  | accepted | declined | blocked | stale | replayed
  deriving DecidableEq, Repr

structure Request (A Task Resource Fact : Type*) where
  actor : A
  generation : Nat
  revision : Nat
  nonce : Nat
  command : Command A Task Resource Fact
  deriving DecidableEq

def Request.key (r : Request A Task Resource Fact) : Nat × A × Nat := (r.generation, r.actor, r.nonce)

structure Machine (A Task Resource Fact : Type*) where
  body : Body A Task Resource Fact
  seen : Finset (Nat × A × Nat)
  history : List (Request A Task Resource Fact × Outcome)

def Current (s : Body A Task Resource Fact) (r : Request A Task Resource Fact) : Prop :=
  r.generation = s.generation ∧ r.revision = s.revision

instance (s : Body A Task Resource Fact) (r : Request A Task Resource Fact) :
    Decidable (Current s r) := by unfold Current; infer_instance

def successOutcome : Command A Task Resource Fact → Outcome
  | .refuse _ => .declined
  | _ => .accepted

def record (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact)
    (outcome : Outcome) (body : Body A Task Resource Fact) : Machine A Task Resource Fact :=
  ⟨body, insert r.key s.seen, s.history ++ [(r, outcome)]⟩

def execute [Fintype Task] (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (r : Request A Task Resource Fact) : Machine A Task Resource Fact :=
  if r.key ∈ s.seen then record s r .replayed s.body
  else if Current s.body r then
    if Allowed profile s.body r.actor r.command then
      record s r (successOutcome r.command) (update s.body r.actor r.command)
    else record s r .blocked s.body
  else record s r .stale s.body

/-- Source rules distinguish refusals, denials, stale requests and replay.
They do not define a step by calling the executable interpreter. -/
inductive Step (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (r : Request A Task Resource Fact) : Machine A Task Resource Fact → Prop where
  | admitted : r.key ∉ s.seen → Current s.body r → Allowed profile s.body r.actor r.command →
      Step profile s r (record s r (successOutcome r.command) (update s.body r.actor r.command))
  | blocked : r.key ∉ s.seen → Current s.body r → ¬ Allowed profile s.body r.actor r.command →
      Step profile s r (record s r .blocked s.body)
  | stale : r.key ∉ s.seen → ¬ Current s.body r → Step profile s r (record s r .stale s.body)
  | replay : r.key ∈ s.seen → Step profile s r (record s r .replayed s.body)

theorem execute_iff [Fintype Task] (profile : ExitProfile) (s t : Machine A Task Resource Fact)
    (r : Request A Task Resource Fact) : execute profile s r = t ↔ Step profile s r t := by
  constructor
  · intro h
    subst t
    by_cases replayed : r.key ∈ s.seen
    · simpa [execute, replayed] using Step.replay (profile := profile) replayed
    · by_cases current : Current s.body r
      · by_cases allowed : Allowed profile s.body r.actor r.command
        · simpa [execute, replayed, current, allowed] using Step.admitted replayed current allowed
        · simpa [execute, replayed, current, allowed] using Step.blocked replayed current allowed
      · simpa [execute, replayed, current] using Step.stale (profile := profile) replayed current
  · intro h
    cases h <;> simp_all [execute]

theorem history_retains_attempt [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact) :
    ∃ outcome, (execute profile s r).history = s.history ++ [(r, outcome)] := by
  unfold execute
  split_ifs <;> exact ⟨_, rfl⟩

theorem replay_has_no_effect [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact) :
    (execute profile (execute profile s r) r).body = (execute profile s r).body := by
  have seen : r.key ∈ (execute profile s r).seen := by
    unfold execute
    split_ifs <;> simp [record]
  rw [execute, if_pos seen]
  rfl

def Authorized (s : Body A Task Resource Fact) (actor : A) (generation : Nat) (resource : Resource) : Prop :=
  Active s actor ∧ generation = s.generation ∧ s.grants resource = some (actor, generation)

instance (s : Body A Task Resource Fact) (actor : A) (generation : Nat) (resource : Resource) :
    Decidable (Authorized s actor generation resource) := by
  unfold Authorized Active
  infer_instance

/-- The caller identity comes from the authenticated transport, separately
from the untrusted payload's actor field. -/
def submit [Fintype Task] (profile : ExitProfile) (principal : A)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact) : Machine A Task Resource Fact :=
  if r.actor = principal then execute profile s r
  else { s with history := s.history ++ [(r, .blocked)] }

theorem impersonation_has_no_effect [Fintype Task] (profile : ExitProfile) (principal : A)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact)
    (wrong : r.actor ≠ principal) : (submit profile principal s r).body = s.body := by
  simp [submit, wrong]

theorem impersonation_cannot_consume_nonce [Fintype Task] (profile : ExitProfile) (principal : A)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact)
    (wrong : r.actor ≠ principal) : (submit profile principal s r).seen = s.seen := by
  simp [submit, wrong]

theorem dissolve_preserves_memory (s : Body A Task Resource Fact) (actor : A) :
    (update s actor .dissolve).knowledge = s.knowledge ∧
    (update s actor .dissolve).commitments = s.commitments ∧
    (update s actor .dissolve).owner = s.owner := ⟨rfl, rfl, rfl⟩

theorem dissolve_expires_grants (s : Body A Task Resource Fact) (actor who : A)
    (epoch : Nat) (resource : Resource) : ¬ Authorized (update s actor .dissolve) who epoch resource := by
  intro h
  exact Bool.false_ne_true h.1.1

theorem fresh_generation (s : Body A Task Resource Fact) (actor : A) :
    (update s actor .dissolve).generation > s.generation := Nat.lt_succ_self _

omit [DecidableEq A] [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem new_generation_not_old_grant (s : Body A Task Resource Fact) (who : A)
    (resource : Resource) :
    ¬ Authorized { s with generation := s.generation + 1 } who s.generation resource := by
  intro h
  have := h.2.1
  simp at this

theorem withdrawal_keeps_commitments (s : Body A Task Resource Fact) (actor : A) :
    (update s actor .withdraw).commitments = s.commitments ∧
    (update s actor .withdraw).responsible = s.responsible := by
  by_cases empty : s.members.erase actor = ∅ <;> simp [update, empty, closeEpisode]

theorem stop_is_local (s : Body A Task Resource Fact) (actor : A) :
    (update s actor .stop).members = s.members ∧
    (update s actor .stop).owner = s.owner ∧ ¬ Active (update s actor .stop) actor := by
  refine ⟨rfl, rfl, ?_⟩
  simp [Active, update]

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem refusal_always_available (profile : ExitProfile) (s : Body A Task Resource Fact)
    (actor : A) (task : Task) : Allowed profile s actor (.refuse task) := True.intro

theorem handover_preserves_obligation (s : Body A Task Resource Fact) (actor previous : A) (task : Task) :
    (update s actor (.takeOver task previous)).commitments task = s.commitments task ∧
    (update s actor (.takeOver task previous)).responsible task = some actor := by
  simp [update]

theorem adoption_clears_old_offers (s : Body A Task Resource Fact) (actor previous successor : A)
    (task : Task) : (task, previous, successor) ∉ (update s actor (.accept task)).offers := by
  simp [update]

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem handover_requires_both_parties (profile : ExitProfile) (s : Body A Task Resource Fact)
    (actor previous : A) (task : Task)
    (allowed : Allowed profile s actor (.takeOver task previous)) :
    (task, previous, actor) ∈ s.offers ∧ s.responsible task = some previous :=
  ⟨allowed.2.1, allowed.2.2.1⟩

theorem transfer_frames_other_resources (s : Body A Task Resource Fact) (actor recipient : A)
    (r other : Resource) (different : other ≠ r) :
    (update s actor (.transfer r recipient)).grants other = s.grants other := by
  simp [update, different]

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem grant_requires_owner (profile : ExitProfile) (s : Body A Task Resource Fact)
    (actor recipient : A) (r : Resource) (h : Allowed profile s actor (.grant r recipient)) :
    s.owner r = actor ∧ s.grants r = none := ⟨h.2.1, h.2.2.1⟩

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem admission_requires_individual_consent (profile : ExitProfile)
    (s : Body A Task Resource Fact) (actor target : A)
    (h : Allowed profile s actor (.admit target)) : target ∈ s.consents := h.2.2.2

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem formation_requires_each_consent (profile : ExitProfile)
    (s : Body A Task Resource Fact) (actor participant : A) (participants : Finset A)
    (h : Allowed profile s actor (.form participants)) (member : participant ∈ participants) :
    participant ∈ s.consents := h.2.2.2.1 member

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem bound_release_preserves_responsibility (s : Body A Task Resource Fact) (actor : A)
    (task : Task) (owner : s.responsible task = some actor) (active : s.commitments task = .active) :
    ¬ Allowed .commitmentBound s actor .withdraw := by
  intro h
  exact h.2 task owner active

omit [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem majority_cannot_bypass_bound_release (s : Body A Task Resource Fact) (actor member : A)
    (task : Task) (inside : member ∈ s.members) (owner : s.responsible task = some member)
    (active : s.commitments task = .active) : ¬ Allowed .commitmentBound s actor .dissolve := by
  intro allowed
  exact allowed.2.2.2 member inside task owner active

def PhaseConsistent (s : Body A Task Resource Fact) : Prop := s.live = true ↔ s.members.Nonempty

theorem update_phase_consistent (profile : ExitProfile) (s : Body A Task Resource Fact)
    (actor : A) (command : Command A Task Resource Fact) (before : PhaseConsistent s)
    (allowed : Allowed profile s actor command) : PhaseConsistent (update s actor command) := by
  cases command with
  | form participants => simpa [PhaseConsistent, update] using allowed.2.2.1
  | admit target => simp [PhaseConsistent, update, allowed.1.1]
  | withdraw =>
    have live : s.live = true := before.mpr ⟨actor, allowed.1⟩
    by_cases empty : s.members.erase actor = ∅
    · simp [PhaseConsistent, update, empty, closeEpisode]
    · simp [PhaseConsistent, update, empty, live, Finset.nonempty_iff_ne_empty]
  | dissolve => simp [PhaseConsistent, update, closeEpisode]
  | _ => simpa [PhaseConsistent, update] using before

theorem execute_phase_consistent [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact)
    (before : PhaseConsistent s.body) : PhaseConsistent (execute profile s r).body := by
  unfold execute
  split_ifs
  all_goals first | exact before | exact update_phase_consistent profile s.body r.actor r.command before (by assumption)

theorem update_knowledge_grows (s : Body A Task Resource Fact) (actor : A)
    (command : Command A Task Resource Fact) : s.knowledge ⊆ (update s actor command).knowledge := by
  cases command with
  | withdraw =>
    by_cases empty : s.members.erase actor = ∅ <;> simp [update, empty, closeEpisode]
  | _ => first | exact Finset.Subset.refl _ | exact Memory.report_monotone _ _ _

theorem update_preserves_owner (s : Body A Task Resource Fact) (actor : A)
    (command : Command A Task Resource Fact) : (update s actor command).owner = s.owner := by
  cases command with
  | withdraw =>
    by_cases empty : s.members.erase actor = ∅ <;> simp [update, empty, closeEpisode]
  | _ => rfl

omit [DecidableEq A] [DecidableEq Task] [DecidableEq Resource] [DecidableEq Fact] in
theorem authorized_exclusive (s : Body A Task Resource Fact) (a b : A)
    (epoch epoch' : Nat) (resource : Resource)
    (ha : Authorized s a epoch resource) (hb : Authorized s b epoch' resource) : a = b := by
  exact congrArg Prod.fst (Option.some.inj (ha.2.2.symm.trans hb.2.2))

theorem active_changes_with_witness (s : Body A Task Resource Fact) (actor : A)
    (command : Command A Task Resource Fact) (task : Task)
    (active : s.commitments task = .active)
    (changed : (update s actor command).commitments task ≠ .active) :
    ∃ witness, command = .discharge task witness := by
  cases command with
  | discharge other witness =>
    by_cases same : task = other
    · subst other
      exact ⟨witness, rfl⟩
    · simp [update, same, active] at changed
  | accept other =>
    by_cases same : task = other <;> simp [update, same, active] at changed
  | withdraw =>
    exact False.elim (changed (by rw [(withdrawal_keeps_commitments s actor).1, active]))
  | dissolve => simp [update, closeEpisode, active] at changed
  | _ => simp [update, active] at changed

theorem execute_knowledge_grows [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (r : Request A Task Resource Fact) :
    s.body.knowledge ⊆ (execute profile s r).body.knowledge := by
  unfold execute
  split_ifs <;> first | exact Finset.Subset.refl _ | exact update_knowledge_grows _ _ _

def run [Fintype Task] (profile : ExitProfile) (s : Machine A Task Resource Fact)
    (requests : List (Request A Task Resource Fact)) : Machine A Task Resource Fact :=
  requests.foldl (execute profile) s

theorem run_phase_consistent [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (requests : List (Request A Task Resource Fact))
    (before : PhaseConsistent s.body) : PhaseConsistent (run profile s requests).body := by
  induction requests generalizing s with
  | nil => exact before
  | cons request rest ih => exact ih (execute profile s request) (execute_phase_consistent profile s request before)

theorem run_knowledge_grows [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (requests : List (Request A Task Resource Fact)) :
    s.body.knowledge ⊆ (run profile s requests).body.knowledge := by
  induction requests generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons r rest ih => exact (execute_knowledge_grows profile s r).trans (ih (execute profile s r))

theorem run_history_length [Fintype Task] (profile : ExitProfile)
    (s : Machine A Task Resource Fact) (requests : List (Request A Task Resource Fact)) :
    (run profile s requests).history.length = s.history.length + requests.length := by
  induction requests generalizing s with
  | nil => simp [run]
  | cons r rest ih =>
    obtain ⟨outcome, h⟩ := history_retains_attempt profile s r
    change (run profile (execute profile s r) rest).history.length = _
    rw [ih, h, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- Package the domain state using the existing five-layer agent interface. -/
def asAgentState (s : Body A Task Resource Fact) :=
  Agent.WorldState.AgentState.mk (s.live, s.members, s.stopped, s.owner) s.knowledge
    (s.responsible, s.commitments, s.offers) (s.generation, s.revision) s.grants

end Mettapedia.CogArch.CollectiveAgency.Lifecycle
