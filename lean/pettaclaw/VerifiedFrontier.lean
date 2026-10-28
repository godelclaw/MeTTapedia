import AgentArchitecture

/-!
# VerifiedFrontier — causal freshness for observable agent effects

This file models the turn property implemented by the Codex core's
`StartOrSteer` path: input submitted while a regular turn is active joins that
turn's pending-input queue, and the turn continues until pending input is
drained.  A model proposal is therefore not yet an observable effect.

The central law is shared with digest-bound self-modification:

> Commit only at a verified frontier, using the exact artifact that was
> checked.

For conversation effects, the frontier is the latest input identity for the
target conversation and quiescence means that no input for that conversation
is pending.  For protected mutation, the frontier is the target's current
revision and artifact identity is its digest.

The model is intentionally smaller than a scheduler or capability system.  It
adds no catalog or authorization lattice.  Liveness is conditional on a fair
quiet point: an environment that supplies fresh input forever can lawfully
prevent completion forever.
-/

namespace VerifiedFrontier

abbrev Conversation := Nat
abbrev EventId := Nat
abbrev TurnId := Nat
abbrev Payload := Nat
abbrev Effect := Nat
abbrev Digest := Nat

inductive Origin
  | operator
  | channel
  | mailbox
deriving Repr, DecidableEq

structure Input where
  id : EventId
  conversation : Conversation
  origin : Origin
  payload : Payload
deriving Repr, DecidableEq

structure Episode where
  turn : TurnId
  conversation : Conversation
  seenFrontier : EventId
deriving Repr, DecidableEq

structure EffectProposal where
  turn : TurnId
  conversation : Conversation
  seenFrontier : EventId
  effect : Effect
  digest : Digest
deriving Repr, DecidableEq

inductive Event
  | input (event : Input)
  | proposed (proposal : EffectProposal)
  | committed (proposal : EffectProposal) (checkedDigest : Digest)
  | completed (turn : TurnId)
deriving Repr, DecidableEq

/-- The authoritative interaction state.  An attention graph is derived from
these coordinates below; it is not a second mutable source of causality. -/
structure State where
  frontier : Conversation → EventId
  log : List Event
  active : Option Episode
  pending : List Input

def initial : State :=
  { frontier := fun _ => 0
    log := []
    active := none
    pending := [] }

def setFrontier (frontier : Conversation → EventId) (input : Input) :
    Conversation → EventId :=
  fun conversation =>
    if conversation = input.conversation then input.id
    else frontier conversation

inductive Submission
  | started (turn : TurnId)
  | steered (turn : TurnId)
deriving Repr, DecidableEq

/-- Start a turn when idle; otherwise preserve the active turn and append the
new input to its pending queue.  Inputs for another conversation remain
queued but do not invalidate the active conversation's frontier. -/
def startOrSteer (state : State) (input : Input) : Submission × State :=
  let nextFrontier := setFrontier state.frontier input
  let nextLog := state.log ++ [.input input]
  match state.active with
  | none =>
      let episode : Episode :=
        { turn := input.id
          conversation := input.conversation
          seenFrontier := input.id }
      (.started episode.turn,
        { state with
          frontier := nextFrontier
          log := nextLog
          active := some episode })
  | some episode =>
      (.steered episode.turn,
        { state with
          frontier := nextFrontier
          log := nextLog
          pending := state.pending ++ [input] })

theorem idle_submission_starts (state : State) (input : Input)
    (idle : state.active = none) :
    (startOrSteer state input).1 = .started input.id ∧
      (startOrSteer state input).2.active = some
        { turn := input.id
          conversation := input.conversation
          seenFrontier := input.id } := by
  simp [startOrSteer, idle]

theorem active_submission_steers (state : State) (input : Input)
    (episode : Episode) (active : state.active = some episode) :
    (startOrSteer state input).1 = .steered episode.turn ∧
      (startOrSteer state input).2.active = some episode ∧
      (startOrSteer state input).2.pending = state.pending ++ [input] := by
  simp [startOrSteer, active]

theorem submission_appends_input_event (state : State) (input : Input) :
    (startOrSteer state input).2.log = state.log ++ [.input input] := by
  cases active : state.active <;> simp [startOrSteer, active]

/-! Stable event identities make intake idempotent across transport retries.
This wrapper is architecture-level: every channel can use it instead of
implementing a different deduplication policy. -/

structure IntakeState where
  core : State
  consumed : List EventId

inductive IntakeSubmission
  | accepted (submission : Submission)
  | duplicate (event : EventId)
deriving Repr, DecidableEq

def submitOnce (state : IntakeState) (input : Input) :
    IntakeSubmission × IntakeState :=
  if input.id ∈ state.consumed then
    (.duplicate input.id, state)
  else
    let submitted := startOrSteer state.core input
    (.accepted submitted.1,
      { core := submitted.2
        consumed := state.consumed ++ [input.id] })

theorem duplicate_input_is_stutter (state : IntakeState) (input : Input)
    (seen : input.id ∈ state.consumed) :
    submitOnce state input = (.duplicate input.id, state) := by
  simp [submitOnce, seen]

theorem fresh_input_is_accepted (state : IntakeState) (input : Input)
    (fresh : input.id ∉ state.consumed) :
    (submitOnce state input).1 = .accepted (startOrSteer state.core input).1 ∧
      (submitOnce state input).2.core = (startOrSteer state.core input).2 ∧
      (submitOnce state input).2.consumed = state.consumed ++ [input.id] := by
  simp [submitOnce, fresh]

theorem replay_after_accept_is_stutter (state : IntakeState) (input : Input)
    (fresh : input.id ∉ state.consumed) :
    let accepted := (submitOnce state input).2
    submitOnce accepted input = (.duplicate input.id, accepted) := by
  simp [submitOnce, fresh]

def Quiescent (state : State) (conversation : Conversation) : Prop :=
  ∀ input, input ∈ state.pending → input.conversation ≠ conversation

theorem steered_same_conversation_is_not_quiescent (state : State)
    (input : Input) (episode : Episode)
    (active : state.active = some episode)
    (same : input.conversation = episode.conversation) :
    ¬ Quiescent (startOrSteer state input).2 episode.conversation := by
  intro quiet
  have member : input ∈ (startOrSteer state input).2.pending := by
    simp [startOrSteer, active]
  exact (quiet input member) same

/-- Pending inputs for the active conversation are incorporated together.
Other conversations remain pending for their own later episode. -/
def drainActive (state : State) : State :=
  match state.active with
  | none => state
  | some episode =>
      { state with
        active := some
          { episode with
            seenFrontier := state.frontier episode.conversation }
        pending := state.pending.filter
          (fun input => input.conversation != episode.conversation) }

theorem drain_active_updates_seen_frontier (state : State)
    (episode : Episode) (active : state.active = some episode) :
    (drainActive state).active = some
      { episode with seenFrontier := state.frontier episode.conversation } := by
  simp [drainActive, active]

theorem drain_active_is_quiescent (state : State) (episode : Episode)
    (active : state.active = some episode) :
    Quiescent (drainActive state) episode.conversation := by
  intro input member same
  simp [drainActive, active, same] at member

/-- The generic commit certificate.  Conversation sends and protected
promotion instantiate the same three equalities/conditions. -/
def VerifiedAtFrontier
    (observedFrontier currentFrontier proposedDigest checkedDigest : Nat)
    (quiescent : Prop) : Prop :=
  observedFrontier = currentFrontier ∧
    proposedDigest = checkedDigest ∧ quiescent

def CurrentEpisode (state : State) (proposal : EffectProposal) : Prop :=
  match state.active with
  | none => False
  | some episode =>
      episode.turn = proposal.turn ∧
        episode.conversation = proposal.conversation ∧
        episode.seenFrontier = proposal.seenFrontier

def AlreadyCommitted (state : State) (proposal : EffectProposal) : Prop :=
  ∃ checkedDigest, .committed proposal checkedDigest ∈ state.log

def CanCommit (check : EffectProposal → Digest)
    (state : State) (proposal : EffectProposal) : Prop :=
  CurrentEpisode state proposal ∧
    VerifiedAtFrontier proposal.seenFrontier
      (state.frontier proposal.conversation)
      proposal.digest (check proposal)
      (Quiescent state proposal.conversation) ∧
    ¬ AlreadyCommitted state proposal

def propose (state : State) (effect : Effect) (digest : Digest) :
    Option EffectProposal :=
  match state.active with
  | none => none
  | some episode => some
      { turn := episode.turn
        conversation := episode.conversation
        seenFrontier := episode.seenFrontier
        effect := effect
        digest := digest }

theorem pending_same_conversation_blocks_commit
    (check : EffectProposal → Digest) (state : State) (input : Input)
    (episode : Episode) (proposal : EffectProposal)
    (active : state.active = some episode)
    (same : input.conversation = proposal.conversation) :
    ¬ CanCommit check (startOrSteer state input).2 proposal := by
  intro permitted
  have quiet : Quiescent (startOrSteer state input).2 proposal.conversation :=
    permitted.2.1.2.2
  have member : input ∈ (startOrSteer state input).2.pending := by
    simp [startOrSteer, active]
  exact (quiet input member) same

/-- After a fair quiet point, draining pending input gives a fresh proposal a
valid certificate when the checker observes the proposal's exact digest. -/
theorem drained_proposal_is_committable (state : State) (episode : Episode)
    (effect : Effect) (digest : Digest)
    (active : state.active = some episode)
    (fresh : ¬ AlreadyCommitted state
      { turn := episode.turn
        conversation := episode.conversation
        seenFrontier := state.frontier episode.conversation
        effect := effect
        digest := digest }) :
    let drained := drainActive state
    let proposal : EffectProposal :=
      { turn := episode.turn
        conversation := episode.conversation
        seenFrontier := state.frontier episode.conversation
        effect := effect
        digest := digest }
    propose drained effect digest = some proposal ∧
      CanCommit (fun candidate => candidate.digest) drained proposal := by
  dsimp
  constructor
  · simp [propose, drainActive, active]
  · constructor
    · simp [CurrentEpisode, drainActive, active]
    · constructor
      · exact ⟨by simp [drainActive, active], rfl,
          drain_active_is_quiescent state episode active⟩
      · simpa [AlreadyCommitted, drainActive, active] using fresh

/-- Observable effects are appended only through a proof-carrying commit. -/
def commit (check : EffectProposal → Digest) (state : State)
    (proposal : EffectProposal) (_ : CanCommit check state proposal) : State :=
  { state with log := state.log ++ [.committed proposal (check proposal)] }

theorem committed_effect_has_current_frontier_exact_artifact_and_quiescence
    (check : EffectProposal → Digest) (state : State)
    (proposal : EffectProposal) (certificate : CanCommit check state proposal) :
    proposal.seenFrontier = state.frontier proposal.conversation ∧
      proposal.digest = check proposal ∧
      Quiescent state proposal.conversation :=
  certificate.2.1

theorem commit_is_append_only (check : EffectProposal → Digest)
    (state : State) (proposal : EffectProposal)
    (certificate : CanCommit check state proposal) :
    (commit check state proposal certificate).log =
      state.log ++ [.committed proposal (check proposal)] := rfl

theorem commit_preserves_active_and_pending (check : EffectProposal → Digest)
    (state : State) (proposal : EffectProposal)
    (certificate : CanCommit check state proposal) :
    (commit check state proposal certificate).active = state.active ∧
      (commit check state proposal certificate).pending = state.pending := by
  exact ⟨rfl, rfl⟩

theorem committed_proposal_cannot_recommit
    (check : EffectProposal → Digest) (state : State)
    (proposal : EffectProposal) (certificate : CanCommit check state proposal) :
    ¬ CanCommit check (commit check state proposal certificate) proposal := by
  intro replay
  exact replay.2.2 ⟨check proposal, by simp [commit]⟩

def CanComplete (state : State) : Prop :=
  match state.active with
  | none => False
  | some episode =>
      episode.seenFrontier = state.frontier episode.conversation ∧
        Quiescent state episode.conversation

/-- Once the environment reaches a quiet point, one drain step supplies the
certificate needed to complete the active turn.  This is the local progress
half of the architecture; reaching a quiet point remains an environment
assumption. -/
theorem drain_active_can_complete (state : State) (episode : Episode)
    (active : state.active = some episode) :
    CanComplete (drainActive state) := by
  simpa [CanComplete, drainActive, active] using
    drain_active_is_quiescent state episode active

def complete (state : State) (certificate : CanComplete state) : State :=
  match active : state.active with
  | none => False.elim (by
      unfold CanComplete at certificate
      rw [active] at certificate
      exact certificate)
  | some episode =>
      { state with
        log := state.log ++ [.completed episode.turn]
        active := none }

theorem completion_requires_current_quiescent_frontier (state : State)
    (episode : Episode) (active : state.active = some episode)
    (certificate : CanComplete state) :
    episode.seenFrontier = state.frontier episode.conversation ∧
      Quiescent state episode.conversation := by
  simpa [CanComplete, active] using certificate

theorem steered_same_conversation_blocks_completion (state : State)
    (input : Input) (episode : Episode)
    (active : state.active = some episode)
    (same : input.conversation = episode.conversation) :
    ¬ CanComplete (startOrSteer state input).2 := by
  intro certificate
  have facts :
      episode.seenFrontier =
          (startOrSteer state input).2.frontier episode.conversation ∧
        Quiescent (startOrSteer state input).2 episode.conversation := by
    simpa [CanComplete, startOrSteer, active] using certificate
  exact steered_same_conversation_is_not_quiescent
    state input episode active same facts.2

/-! ## Proof-carrying traces -/

theorem complete_is_append_only (state : State)
    (certificate : CanComplete state) :
    state.log.IsPrefix (complete state certificate).log := by
  cases state with
  | mk frontier log active pending =>
      cases active with
      | none => simp [CanComplete] at certificate
      | some episode =>
          change log.IsPrefix (log ++ [.completed episode.turn])
          exact List.prefix_append log [.completed episode.turn]

/-- Every legal interaction transition either accepts input, drains pending
input into the active request, commits with a certificate, or completes with a
quiescence certificate. -/
inductive Step (check : EffectProposal → Digest) : State → State → Prop
  | submit (state : State) (input : Input) :
      Step check state (startOrSteer state input).2
  | drain (state : State) :
      Step check state (drainActive state)
  | commit (state : State) (proposal : EffectProposal)
      (certificate : CanCommit check state proposal) :
      Step check state
        (VerifiedFrontier.commit check state proposal certificate)
  | complete (state : State) (certificate : CanComplete state) :
      Step check state (VerifiedFrontier.complete state certificate)

theorem step_log_is_append_only (check : EffectProposal → Digest)
    {before after : State} (transition : Step check before after) :
    before.log.IsPrefix after.log := by
  cases transition with
  | submit input =>
      cases active : before.active <;>
        simp [startOrSteer, active, List.IsPrefix]
  | drain =>
      cases active : before.active <;>
        simp [drainActive, active, List.IsPrefix]
  | commit proposal certificate =>
      simp [VerifiedFrontier.commit, List.IsPrefix]
  | complete certificate =>
      exact complete_is_append_only before certificate

inductive Reachable (check : EffectProposal → Digest) (start : State) :
    State → Prop
  | refl : Reachable check start start
  | tail {before after : State} :
      Reachable check start before →
      Step check before after →
      Reachable check start after

theorem reachable_log_extends_initial (check : EffectProposal → Digest)
    (start after : State) (trace : Reachable check start after) :
    start.log.IsPrefix after.log := by
  induction trace with
  | refl => exact List.prefix_rfl
  | tail prior transition ih =>
      exact ih.trans (step_log_is_append_only check transition)

/-! ## Why the frontier coordinate is necessary -/

/-- The behavior being excluded: append an observable effect without checking
the request frontier, quiescence, or artifact identity. -/
def naiveCommit (state : State) (proposal : EffectProposal)
    (checkedDigest : Digest) : State :=
  { state with log := state.log ++ [.committed proposal checkedDigest] }

theorem naive_stale_effect_is_reachable :
    let first : Input := ⟨1, 7, .operator, 11⟩
    let second : Input := ⟨2, 7, .operator, 12⟩
    let started := (startOrSteer initial first).2
    let proposal : EffectProposal := ⟨1, 7, 1, 9, 13⟩
    let stale := (startOrSteer started second).2
    proposal.seenFrontier ≠ stale.frontier proposal.conversation ∧
      (naiveCommit stale proposal 13).log =
        stale.log ++ [.committed proposal 13] := by
  decide

/-- The eligibility coordinates that a frontier-blind gate might still use. -/
def EligibleIgnoringFrontier (state : State)
    (proposal : EffectProposal) : Prop :=
  CurrentEpisode state proposal ∧
    Quiescent state proposal.conversation ∧
    ¬ AlreadyCommitted state proposal

/-- A gate is frontier-blind when changing only the frontier cannot change its
decision. -/
def FrontierBlind (gate : State → EffectProposal → Prop) : Prop :=
  ∀ left right proposal,
    left.active = right.active →
    left.pending = right.pending →
    left.log = right.log →
    (gate left proposal ↔ gate right proposal)

def FrontierComplete (gate : State → EffectProposal → Prop) : Prop :=
  ∀ state proposal,
    EligibleIgnoringFrontier state proposal →
    proposal.seenFrontier = state.frontier proposal.conversation →
    gate state proposal

def FrontierSound (gate : State → EffectProposal → Prop) : Prop :=
  ∀ state proposal,
    EligibleIgnoringFrontier state proposal →
    proposal.seenFrontier ≠ state.frontier proposal.conversation →
    ¬ gate state proposal

/-- No gate that ignores the frontier can both admit every otherwise-eligible
fresh proposal and reject every otherwise-eligible stale proposal. -/
theorem no_frontier_blind_gate_is_complete_and_sound :
    ¬ ∃ gate : State → EffectProposal → Prop,
      FrontierBlind gate ∧ FrontierComplete gate ∧ FrontierSound gate := by
  rintro ⟨gate, blind, complete, sound⟩
  let episode : Episode := ⟨1, 7, 1⟩
  let proposal : EffectProposal := ⟨1, 7, 1, 9, 13⟩
  let fresh : State :=
    { frontier := fun conversation => if conversation = 7 then 1 else 0
      log := []
      active := some episode
      pending := [] }
  let stale : State :=
    { fresh with
      frontier := fun conversation => if conversation = 7 then 2 else 0 }
  have eligibleFresh : EligibleIgnoringFrontier fresh proposal := by
    simp [EligibleIgnoringFrontier, fresh, proposal, episode,
      CurrentEpisode, Quiescent, AlreadyCommitted]
  have eligibleStale : EligibleIgnoringFrontier stale proposal := by
    simp [EligibleIgnoringFrontier, stale, fresh, proposal, episode,
      CurrentEpisode, Quiescent, AlreadyCommitted]
  have currentFresh :
      proposal.seenFrontier = fresh.frontier proposal.conversation := by
    simp [fresh, proposal]
  have staleMismatch :
      proposal.seenFrontier ≠ stale.frontier proposal.conversation := by
    simp [stale, proposal]
  have acceptedFresh : gate fresh proposal :=
    complete fresh proposal eligibleFresh currentFresh
  have acceptedStale : gate stale proposal :=
    (blind fresh stale proposal rfl rfl rfl).mp acceptedFresh
  exact (sound stale proposal eligibleStale staleMismatch) acceptedStale

/-! ## Outcome-first evaluation -/

structure Evaluation where
  accepted : Bool
  evidenceComplete : Bool
  calls : Nat
  retries : Nat
deriving Repr, DecidableEq

def MeetsQualityBar (evaluation : Evaluation) : Prop :=
  evaluation.accepted = true ∧ evaluation.evidenceComplete = true

/-- Resource use is an improvement only inside the quality-preserving region. -/
def EfficiencyImprovement (candidate baseline : Evaluation) : Prop :=
  MeetsQualityBar candidate ∧ MeetsQualityBar baseline ∧
    candidate.calls + candidate.retries ≤ baseline.calls + baseline.retries

theorem fewer_calls_without_verified_quality_is_not_an_improvement :
    let baseline : Evaluation := ⟨true, true, 3, 0⟩
    let candidate : Evaluation := ⟨false, false, 1, 0⟩
    candidate.calls < baseline.calls ∧
      ¬ EfficiencyImprovement candidate baseline := by
  simp [EfficiencyImprovement, MeetsQualityBar]

/-! ## Exact-once room ingestion and non-draining wake energy -/

structure RoomMessage where
  input : Input
  inbound : Bool
deriving Repr, DecidableEq

structure AdapterState where
  consumed : List EventId
  queued : List Input
  energy : Nat
deriving Repr, DecidableEq

def ingest (tier : Nat) (state : AdapterState) (message : RoomMessage) :
    AdapterState :=
  if message.inbound then
    if message.input.id ∈ state.consumed then state
    else
      { consumed := state.consumed ++ [message.input.id]
        queued := state.queued ++ [message.input]
        energy := Nat.max state.energy tier }
  else state

theorem outbound_echo_is_stutter (tier : Nat) (state : AdapterState)
    (message : RoomMessage) (echo : message.inbound = false) :
    ingest tier state message = state := by
  simp [ingest, echo]

theorem consumed_identity_is_stutter (tier : Nat) (state : AdapterState)
    (message : RoomMessage) (seen : message.input.id ∈ state.consumed) :
    ingest tier state message = state := by
  cases inbound : message.inbound <;> simp [ingest, inbound, seen]

theorem fresh_inbound_queues_once_and_arms_by_max (tier : Nat)
    (state : AdapterState) (message : RoomMessage)
    (inbound : message.inbound = true)
    (fresh : message.input.id ∉ state.consumed) :
    let next := ingest tier state message
    next.consumed = state.consumed ++ [message.input.id] ∧
      next.queued = state.queued ++ [message.input] ∧
      next.energy = Nat.max state.energy tier := by
  simp [ingest, inbound, fresh]

theorem room_wake_never_drains_energy (tier : Nat) (state : AdapterState)
    (message : RoomMessage) :
    state.energy ≤ (ingest tier state message).energy := by
  by_cases inbound : message.inbound
  · by_cases seen : message.input.id ∈ state.consumed
    · simp [ingest, inbound, seen]
    · simp [ingest, inbound, seen, Nat.le_max_left]
  · simp [ingest, inbound]

theorem reconnect_cannot_replay_fresh_inbound (tier : Nat)
    (state : AdapterState) (message : RoomMessage)
    (inbound : message.inbound = true)
    (fresh : message.input.id ∉ state.consumed) :
    ingest tier (ingest tier state message) message =
      ingest tier state message := by
  simp [ingest, inbound, fresh]

/-! ## Digest-bound promotion is the same invariant family -/

abbrev Target := Nat

structure MutationProposal where
  target : Target
  basedOnRevision : Nat
  digest : Digest
deriving Repr, DecidableEq

structure Deployment where
  revision : Target → Nat
  installedDigest : Target → Digest

def CanPromote (check : MutationProposal → Digest)
    (deployment : Deployment) (proposal : MutationProposal) : Prop :=
  VerifiedAtFrontier proposal.basedOnRevision
    (deployment.revision proposal.target)
    proposal.digest (check proposal) True

def promote (check : MutationProposal → Digest) (deployment : Deployment)
    (proposal : MutationProposal)
    (_ : CanPromote check deployment proposal) : Deployment :=
  { revision := fun target =>
      if target = proposal.target
      then deployment.revision target + 1
      else deployment.revision target
    installedDigest := fun target =>
      if target = proposal.target
      then proposal.digest
      else deployment.installedDigest target }

theorem promotion_requires_current_revision_and_exact_digest
    (check : MutationProposal → Digest) (deployment : Deployment)
    (proposal : MutationProposal)
    (certificate : CanPromote check deployment proposal) :
    proposal.basedOnRevision = deployment.revision proposal.target ∧
      proposal.digest = check proposal := by
  exact ⟨certificate.1, certificate.2.1⟩

theorem promotion_installs_exact_proposed_digest
    (check : MutationProposal → Digest) (deployment : Deployment)
    (proposal : MutationProposal)
    (certificate : CanPromote check deployment proposal) :
    (promote check deployment proposal certificate).installedDigest
      proposal.target = proposal.digest := by
  simp [promote]

/-! ## Derived attention and conservative fusion -/

structure AttentionView where
  active : Option Episode
  pendingIds : List EventId
  causalLog : List Event
deriving Repr, DecidableEq

def attentionView (state : State) : AttentionView :=
  { active := state.active
    pendingIds := state.pending.map Input.id
    causalLog := state.log }

theorem attention_is_a_derived_view (left right : State)
    (sameActive : left.active = right.active)
    (samePending : left.pending = right.pending)
    (sameLog : left.log = right.log) :
    attentionView left = attentionView right := by
  simp [attentionView, sameActive, samePending, sameLog]

/-- The minimal product architecture.  Existing components remain separate
coordinates: protected plasticity, epistemic receipts, and interaction
freshness. -/
structure Merged (K D L : Type) where
  coordinates : ProtectedPlasticity.Coordinates K D L
  epistemic : AgentArchitecture.State
  interaction : State

def revise {K D L : Type} (state : Merged K D L) (change : D → D) :
    Merged K D L :=
  { state with
    coordinates := ProtectedPlasticity.revise state.coordinates change }

def evolve {K D L : Type} (state : Merged K D L) (change : L → L) :
    Merged K D L :=
  { state with
    coordinates := ProtectedPlasticity.evolve state.coordinates change }

def updateEpistemic {K D L : Type} (state : Merged K D L)
    (change : AgentArchitecture.State → AgentArchitecture.State) :
    Merged K D L :=
  { state with epistemic := change state.epistemic }

def updateInteraction {K D L : Type} (state : Merged K D L)
    (change : State → State) : Merged K D L :=
  { state with interaction := change state.interaction }

theorem interaction_and_development_commute {K D L : Type}
    (state : Merged K D L) (developmental : D → D)
    (interaction : State → State) :
    updateInteraction (revise state developmental) interaction =
      revise (updateInteraction state interaction) developmental := by
  rfl

theorem interaction_and_life_commute {K D L : Type}
    (state : Merged K D L) (living : L → L)
    (interaction : State → State) :
    updateInteraction (evolve state living) interaction =
      evolve (updateInteraction state interaction) living := by
  rfl

theorem interaction_and_epistemic_commute {K D L : Type}
    (state : Merged K D L)
    (epistemic : AgentArchitecture.State → AgentArchitecture.State)
    (interaction : State → State) :
    updateInteraction (updateEpistemic state epistemic) interaction =
      updateEpistemic (updateInteraction state interaction) epistemic := by
  rfl

def mergedCommit {K D L : Type} (check : EffectProposal → Digest)
    (state : Merged K D L) (proposal : EffectProposal)
    (certificate : CanCommit check state.interaction proposal) : Merged K D L :=
  { state with
    interaction := commit check state.interaction proposal certificate }

theorem merged_commit_preserves_kernel_life_and_epistemic {K D L : Type}
    (check : EffectProposal → Digest) (state : Merged K D L)
    (proposal : EffectProposal)
    (certificate : CanCommit check state.interaction proposal) :
    let next := mergedCommit check state proposal certificate
    next.coordinates.kernel = state.coordinates.kernel ∧
      next.coordinates.life = state.coordinates.life ∧
      next.epistemic = state.epistemic := by
  exact ⟨rfl, rfl, rfl⟩

/-- Iter transformation remains the developmental projection of the fusion. -/
def iterTransform {K L : Type}
    (state : Merged K IterArchitecture.Boundary L)
    (transformation : IterArchitecture.Transformation) :
    Merged K IterArchitecture.Boundary L :=
  revise state (fun boundary =>
    IterArchitecture.applyTransformation boundary transformation)

theorem iter_transform_preserves_frontier_receipts_kernel_and_life {K L : Type}
    (state : Merged K IterArchitecture.Boundary L)
    (transformation : IterArchitecture.Transformation) :
    let next := iterTransform state transformation
    next.interaction.log = state.interaction.log ∧
      next.coordinates.kernel = state.coordinates.kernel ∧
      next.coordinates.life = state.coordinates.life := by
  exact ⟨rfl, rfl, rfl⟩

end VerifiedFrontier

/-! ## Axiom audit -/
#print axioms VerifiedFrontier.idle_submission_starts
#print axioms VerifiedFrontier.active_submission_steers
#print axioms VerifiedFrontier.duplicate_input_is_stutter
#print axioms VerifiedFrontier.replay_after_accept_is_stutter
#print axioms VerifiedFrontier.steered_same_conversation_is_not_quiescent
#print axioms VerifiedFrontier.drain_active_is_quiescent
#print axioms VerifiedFrontier.drain_active_can_complete
#print axioms VerifiedFrontier.pending_same_conversation_blocks_commit
#print axioms VerifiedFrontier.drained_proposal_is_committable
#print axioms VerifiedFrontier.committed_effect_has_current_frontier_exact_artifact_and_quiescence
#print axioms VerifiedFrontier.committed_proposal_cannot_recommit
#print axioms VerifiedFrontier.steered_same_conversation_blocks_completion
#print axioms VerifiedFrontier.step_log_is_append_only
#print axioms VerifiedFrontier.reachable_log_extends_initial
#print axioms VerifiedFrontier.naive_stale_effect_is_reachable
#print axioms VerifiedFrontier.no_frontier_blind_gate_is_complete_and_sound
#print axioms VerifiedFrontier.fewer_calls_without_verified_quality_is_not_an_improvement
#print axioms VerifiedFrontier.reconnect_cannot_replay_fresh_inbound
#print axioms VerifiedFrontier.promotion_requires_current_revision_and_exact_digest
#print axioms VerifiedFrontier.attention_is_a_derived_view
#print axioms VerifiedFrontier.interaction_and_development_commute
#print axioms VerifiedFrontier.merged_commit_preserves_kernel_life_and_epistemic
#print axioms VerifiedFrontier.iter_transform_preserves_frontier_receipts_kernel_and_life
