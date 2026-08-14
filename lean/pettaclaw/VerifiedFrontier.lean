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

def CanCommit (check : EffectProposal → Digest)
    (state : State) (proposal : EffectProposal) : Prop :=
  CurrentEpisode state proposal ∧
    VerifiedAtFrontier proposal.seenFrontier
      (state.frontier proposal.conversation)
      proposal.digest (check proposal)
      (Quiescent state proposal.conversation)

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
    permitted.2.2.2
  have member : input ∈ (startOrSteer state input).2.pending := by
    simp [startOrSteer, active]
  exact (quiet input member) same

/-- After a fair quiet point, draining pending input gives a fresh proposal a
valid certificate when the checker observes the proposal's exact digest. -/
theorem drained_proposal_is_committable (state : State) (episode : Episode)
    (effect : Effect) (digest : Digest)
    (active : state.active = some episode) :
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
    · exact ⟨by simp [drainActive, active], rfl,
        drain_active_is_quiescent state episode active⟩

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
  certificate.2

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

def CanComplete (state : State) : Prop :=
  match state.active with
  | none => False
  | some episode =>
      episode.seenFrontier = state.frontier episode.conversation ∧
        Quiescent state episode.conversation

def complete (state : State) (certificate : CanComplete state) : State :=
  match active : state.active with
  | none => False.elim (by simpa [CanComplete, active] using certificate)
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
#print axioms VerifiedFrontier.steered_same_conversation_is_not_quiescent
#print axioms VerifiedFrontier.drain_active_is_quiescent
#print axioms VerifiedFrontier.pending_same_conversation_blocks_commit
#print axioms VerifiedFrontier.drained_proposal_is_committable
#print axioms VerifiedFrontier.committed_effect_has_current_frontier_exact_artifact_and_quiescence
#print axioms VerifiedFrontier.steered_same_conversation_blocks_completion
#print axioms VerifiedFrontier.reconnect_cannot_replay_fresh_inbound
#print axioms VerifiedFrontier.promotion_requires_current_revision_and_exact_digest
#print axioms VerifiedFrontier.attention_is_a_derived_view
#print axioms VerifiedFrontier.interaction_and_development_commute
#print axioms VerifiedFrontier.merged_commit_preserves_kernel_life_and_epistemic
#print axioms VerifiedFrontier.iter_transform_preserves_frontier_receipts_kernel_and_life
