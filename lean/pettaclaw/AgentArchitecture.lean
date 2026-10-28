import ContextAttention

/-!
# AgentArchitecture — a minimal contract for reliable agent loops

This file isolates four obligations that are independent of model quality and
of the language used to implement an agent:

* load-bearing constraints are structurally separate from lossy working
  context;
* the durable receipt log grows monotonically while compaction changes only a
  derived view;
* process activity, model activity, verified progress, and reported completion
  are distinct observations;
* a completion report is admitted only after an ordered external-evidence
  chain.

The contract is deliberately smaller than a capability system.  It says
nothing about which tools an agent may possess, how goals are chosen, or which
model is sampled.  PettaClaw supplies a life scheduler, Iter supplies
transformations of the derived request boundary, ContextAttention supplies
interruptibility, and CodingAgent supplies brokered effects.  The definitions
below state the additional epistemic conditions needed before a loop may call
its work complete.

The empirical claim that particular detectors predict failure is outside this
formal boundary.  Repetition detectors below produce a `suspicious` signal,
not a theorem that the underlying task is stuck.
-/

namespace AgentArchitecture

abbrev Goal := Nat
abbrev Action := Nat
abbrev Observation := Nat
abbrev Error := Nat
abbrev Constraint := Nat

/-! ## Durable receipts and end-to-end evidence -/

inductive Receipt
  | intention (goal : Goal)
  | attempted (goal : Goal) (action : Action)
  | observed (goal : Goal) (action : Action) (observation : Observation)
  | accepted (goal : Goal) (action : Action) (observation : Observation)
  | failed (goal : Goal) (action : Action) (error : Error)
  | claimed (goal : Goal)
deriving Repr, DecidableEq

/-- A completion chain is ordered, not merely a bag of related receipts. -/
def EndToEnd (log : List Receipt) (goal : Goal) : Prop :=
  ∃ action observation,
    ([.intention goal, .attempted goal action,
      .observed goal action observation, .accepted goal action observation] :
      List Receipt).Sublist log

/-- `accepts` is the external checker's semantic contract.  A verified chain
requires both the ordered receipt trace and acceptance of the exact terminal
triple.  Soundness of `accepts` with respect to the real task is the explicit
trusted boundary. -/
def VerifiedEndToEnd
    (accepts : Goal → Action → Observation → Prop)
    (log : List Receipt) (goal : Goal) : Prop :=
  ∃ action observation,
    ([.intention goal, .attempted goal action,
      .observed goal action observation, .accepted goal action observation] :
      List Receipt).Sublist log ∧ accepts goal action observation

theorem canonical_chain_is_end_to_end (goal action observation : Nat) :
    EndToEnd
      [.intention goal, .attempted goal action,
        .observed goal action observation, .accepted goal action observation]
      goal := by
  exact ⟨action, observation, List.Sublist.refl _⟩

theorem canonical_chain_is_verified
    (accepts : Goal → Action → Observation → Prop)
    (goal action observation : Nat)
    (verified : accepts goal action observation) :
    VerifiedEndToEnd accepts
      [.intention goal, .attempted goal action,
        .observed goal action observation, .accepted goal action observation]
      goal := by
  exact ⟨action, observation, List.Sublist.refl _, verified⟩

/-! ## Source of truth versus working view -/

/-- `required` is reloaded independently of compaction.  `log` is the durable
source of truth; `view` is a disposable request-local projection. -/
structure State where
  required : List Constraint
  log : List Receipt
  view : List Receipt
  processTicks : Nat
  modelTurns : Nat
deriving Repr, DecidableEq

def initial (required : List Constraint) : State :=
  ⟨required, [], [], 0, 0⟩

def heartbeat (state : State) : State :=
  { state with processTicks := state.processTicks + 1 }

/-- A model turn is also process activity, but not necessarily progress. -/
def modelTurn (state : State) : State :=
  { state with
    processTicks := state.processTicks + 1
    modelTurns := state.modelTurns + 1 }

def record (state : State) (receipt : Receipt) : State :=
  { state with log := state.log ++ [receipt] }

/-- Compaction may be arbitrary and lossy, but receives only the durable log
and writes only the derived view. -/
def refresh (select : List Receipt → List Receipt) (state : State) : State :=
  { state with view := select state.log }

structure RequestView where
  required : List Constraint
  evidence : List Receipt
deriving Repr, DecidableEq

/-- Request assembly pins protected constraints outside the compacted evidence
view. -/
def assemble (state : State) : RequestView :=
  ⟨state.required, state.view⟩

theorem record_is_append_only (state : State) (receipt : Receipt) :
    (record state receipt).log = state.log ++ [receipt] := rfl

theorem refresh_preserves_durable_log
    (select : List Receipt → List Receipt) (state : State) :
    (refresh select state).log = state.log := rfl

theorem refresh_preserves_protected_constraints
    (select : List Receipt → List Receipt) (state : State) :
    (refresh select state).required = state.required := rfl

theorem assembly_pins_constraints_after_arbitrary_compaction
    (select : List Receipt → List Receipt) (state : State) :
    (assemble (refresh select state)).required = state.required := rfl

/-- A lossy compaction can erase every working receipt while the durable source
of truth remains intact.  Thus a working view alone is not a continuity
mechanism. -/
theorem compaction_can_erase_view_but_not_log :
    let state := record (initial [11]) (.intention 7)
    let next := refresh (fun _ => []) state
    next.view = [] ∧ next.log = [.intention 7] ∧
      (assemble next).required = [11] := by
  decide

/-- If constraints share the lossy coordinate, no arbitrary compactor can
guarantee their survival.  Structural pinning is the relevant difference. -/
theorem naive_context_compaction_can_drop_constraint :
    let context : List Constraint := [11]
    11 ∈ context ∧ 11 ∉ (fun _ : List Constraint => []) context := by
  decide

/-! ## Four observations that must not be conflated -/

def ProcessLive (before after : State) : Prop :=
  before.processTicks < after.processTicks

def CognitiveLive (before after : State) : Prop :=
  before.modelTurns < after.modelTurns

def VerifiedProgress (accepts : Goal → Action → Observation → Prop)
    (before after : State) : Prop :=
  ∃ goal action observation,
    accepts goal action observation ∧
      .accepted goal action observation ∉ before.log ∧
      .accepted goal action observation ∈ after.log

def ReportsCompletion (before after : State) (goal : Goal) : Prop :=
  after.log = before.log ++ [.claimed goal]

theorem heartbeat_can_be_process_live_without_cognition :
    let state := initial []
    ProcessLive state (heartbeat state) ∧
      ¬ CognitiveLive state (heartbeat state) := by
  simp [ProcessLive, CognitiveLive, initial, heartbeat]

theorem model_turn_can_be_cognitively_live_without_verified_progress :
    let state := initial []
    CognitiveLive state (modelTurn state) ∧
      ¬ VerifiedProgress (fun _ _ _ => True) state (modelTurn state) := by
  simp [CognitiveLive, VerifiedProgress, initial, modelTurn]

theorem accepted_receipt_is_progress_before_any_completion_report :
    let state := initial []
    let next := record state (.accepted 7 3 9)
    VerifiedProgress (fun goal action observation =>
      goal = 7 ∧ action = 3 ∧ observation = 9) state next ∧
      ¬ ReportsCompletion state next 7 := by
  simp [VerifiedProgress, ReportsCompletion, initial, record]

/-! ## Completion gate and the silent-false-success separation -/

/-- Completion is proof-carrying: no successor can be constructed through this
operation without an externally verified, ordered chain in the durable
pre-state. -/
def claim (accepts : Goal → Action → Observation → Prop)
    (state : State) (goal : Goal)
    (_ : VerifiedEndToEnd accepts state.log goal) : State :=
  record state (.claimed goal)

theorem admitted_claim_has_end_to_end_evidence
    (accepts : Goal → Action → Observation → Prop)
    (state : State) (goal : Goal)
    (evidence : VerifiedEndToEnd accepts state.log goal) :
    VerifiedEndToEnd accepts state.log goal :=
  evidence

def SilentFalseSuccess (accepts : Goal → Action → Observation → Prop)
    (before after : State) (goal : Goal) : Prop :=
  ReportsCompletion before after goal ∧
    ¬ VerifiedEndToEnd accepts before.log goal

theorem claim_gate_prevents_silent_false_success
    (accepts : Goal → Action → Observation → Prop)
    (state : State) (goal : Goal)
    (evidence : VerifiedEndToEnd accepts state.log goal) :
    ¬ SilentFalseSuccess accepts state (claim accepts state goal evidence) goal := by
  intro silent
  exact silent.2 evidence

def naiveClaim (state : State) (goal : Goal) : State :=
  record state (.claimed goal)

/-- Termination or assertion without a receipt gate admits the dominant
false-success shape immediately. -/
theorem naive_completion_permits_silent_false_success :
    SilentFalseSuccess (fun _ _ _ => False)
      (initial []) (naiveClaim (initial []) 7) 7 := by
  simp [SilentFalseSuccess, ReportsCompletion, naiveClaim, record, initial,
    VerifiedEndToEnd]

/-! ## A minimal transition discipline -/

/-- `Step` is the reference transition relation.  Evidence may be appended,
views may be rebuilt, and activity counters may advance.  A claim is the only
special receipt: its constructor requires its proof obligation. -/
def OrdinaryReceipt : Receipt → Prop
  | .intention _ | .attempted _ _ | .observed _ _ _ | .failed _ _ _ => True
  | .accepted _ _ _ | .claimed _ => False

inductive Step (accepts : Goal → Action → Observation → Prop) :
    State → State → Prop
  | heartbeat (state : State) :
      Step accepts state (AgentArchitecture.heartbeat state)
  | modelTurn (state : State) :
      Step accepts state (AgentArchitecture.modelTurn state)
  | evidence (state : State) (receipt : Receipt)
      (ordinary : OrdinaryReceipt receipt) :
      Step accepts state (record state receipt)
  | acceptance (state : State) (goal : Goal) (action : Action)
      (observation : Observation) (verified : accepts goal action observation) :
      Step accepts state (record state (.accepted goal action observation))
  | refresh (state : State) (select : List Receipt → List Receipt) :
      Step accepts state (AgentArchitecture.refresh select state)
  | claim (state : State) (goal : Goal)
      (evidence : VerifiedEndToEnd accepts state.log goal) :
      Step accepts state (record state (.claimed goal))

theorem step_preserves_protected_constraints
    (accepts : Goal → Action → Observation → Prop)
    {before after : State} (step : Step accepts before after) :
    after.required = before.required := by
  cases step <;> rfl

theorem step_preserves_or_extends_log
    (accepts : Goal → Action → Observation → Prop)
    {before after : State} (step : Step accepts before after) :
    before.log.IsPrefix after.log := by
  cases step <;>
    simp [List.IsPrefix, AgentArchitecture.heartbeat,
      AgentArchitecture.modelTurn, AgentArchitecture.refresh, record]

theorem step_claim_requires_end_to_end_evidence
    (accepts : Goal → Action → Observation → Prop)
    {before after : State} (step : Step accepts before after) (goal : Goal)
    (reported : ReportsCompletion before after goal) :
    VerifiedEndToEnd accepts before.log goal := by
  cases step <;>
    simp_all [ReportsCompletion, AgentArchitecture.heartbeat,
      AgentArchitecture.modelTurn, AgentArchitecture.refresh, record,
      OrdinaryReceipt]

/-- An acceptance receipt cannot enter through the ordinary evidence lane.
The transition that appends it carries the external verifier's witness for the
same goal, action, and observation. -/
theorem step_acceptance_requires_external_verification
    (accepts : Goal → Action → Observation → Prop)
    {before after : State} (step : Step accepts before after)
    (goal : Goal) (action : Action) (observation : Observation)
    (recorded :
      after.log = before.log ++ [.accepted goal action observation]) :
    accepts goal action observation := by
  cases step <;>
    simp_all [AgentArchitecture.heartbeat, AgentArchitecture.modelTurn,
      AgentArchitecture.refresh, record, OrdinaryReceipt]

/-! ## The reusable architecture contract -/

/-- Any concrete agent loop can instantiate this contract without adopting the
reference state representation. -/
structure LoopContract (σ : Type) where
  accepts : Goal → Action → Observation → Prop
  next : σ → σ → Prop
  required : σ → List Constraint
  visible : σ → List Constraint
  log : σ → List Receipt
  kernelStable : ∀ {before after}, next before after →
    required after = required before
  constraintsVisible : ∀ state, visible state = required state
  appendOnly : ∀ {before after}, next before after →
    (log before).IsPrefix (log after)
  claimSound : ∀ {before after} goal, next before after →
    log after = log before ++ [.claimed goal] →
      VerifiedEndToEnd accepts (log before) goal

def referenceContract
    (accepts : Goal → Action → Observation → Prop) : LoopContract State where
  accepts := accepts
  next := Step accepts
  required := State.required
  visible := fun state => (assemble state).required
  log := State.log
  kernelStable := step_preserves_protected_constraints accepts
  constraintsVisible := fun _ => rfl
  appendOnly := step_preserves_or_extends_log accepts
  claimSound := fun goal step reported =>
    step_claim_requires_end_to_end_evidence accepts step goal reported

theorem LoopContract.no_silent_false_success {σ : Type}
    (contract : LoopContract σ) {before after : σ} (goal : Goal)
    (step : contract.next before after) :
    ¬ (contract.log after = contract.log before ++ [.claimed goal] ∧
      ¬ VerifiedEndToEnd contract.accepts (contract.log before) goal) := by
  intro silent
  exact silent.2 (contract.claimSound goal step silent.1)

theorem LoopContract.constraints_survive_and_are_visible {σ : Type}
    (contract : LoopContract σ) {before after : σ}
    (step : contract.next before after) :
    contract.visible after = contract.required before := by
  rw [contract.constraintsVisible, contract.kernelStable step]

/-! ## Syntactic stuck signals -/

def sameObservation : Receipt → Receipt → Bool
  | .observed goal action observation,
      .observed goal' action' observation' =>
      decide (goal = goal' ∧ action = action' ∧ observation = observation')
  | _, _ => false

def sameFailure : Receipt → Receipt → Bool
  | .failed goal action error, .failed goal' action' error' =>
      decide (goal = goal' ∧ action = action' ∧ error = error')
  | _, _ => false

def sameAttempt : Receipt → Receipt → Bool
  | .attempted goal action, .attempted goal' action' =>
      decide (goal = goal' ∧ action = action')
  | _, _ => false

def isAttempt : Receipt → Bool
  | .attempted _ _ => true
  | _ => false

def repeatedObservationFour (log : List Receipt) : Bool :=
  match log.reverse with
  | first :: second :: third :: fourth :: _ =>
      sameObservation first second && sameObservation second third &&
        sameObservation third fourth
  | _ => false

def repeatedFailureThree (log : List Receipt) : Bool :=
  match log.reverse with
  | first :: second :: third :: _ =>
      sameFailure first second && sameFailure second third
  | _ => false

def pingPongFour (log : List Receipt) : Bool :=
  match log.reverse with
  | fourth :: third :: second :: first :: _ =>
      isAttempt first && isAttempt second &&
        sameAttempt first third && sameAttempt second fourth &&
        !sameAttempt first second
  | _ => false

/-- A runtime escalation signal, intentionally not named `Stuck`. -/
def suspicious (log : List Receipt) : Bool :=
  repeatedObservationFour log || repeatedFailureThree log || pingPongFour log

theorem four_identical_observations_are_suspicious :
    suspicious (List.replicate 4 (.observed 7 3 9)) = true := by
  decide

theorem three_identical_failures_are_suspicious :
    suspicious (List.replicate 3 (.failed 7 3 9)) = true := by
  decide

theorem alternating_attempts_are_suspicious :
    suspicious
      [.attempted 7 3, .attempted 7 4, .attempted 7 3, .attempted 7 4] =
      true := by
  decide

/-! ## Relation to the three concrete loops -/

/-- The CodingAgent core establishes terminality without verification.  The
new claim contract is therefore an additional layer, not a restatement of its
broker/evidence barrier. -/
theorem coding_agent_core_allows_unverified_termination :
    ∃ state : CodingAgent.State,
      state.phase = .done 7 ∧
        ¬ (state.history.any CodingAgent.isToolEvidence) :=
  CodingAgent.unverified_answer_is_reachable

/-- Arbitrary Iter preparation may rewrite the working request boundary, while
the protected constraint coordinate remains unchanged. -/
theorem iter_transformation_is_confined_to_working_view
    (transformation : IterArchitecture.Transformation)
    (boundary : IterArchitecture.Boundary) (state : State) :
    (IterArchitecture.applyTransformation boundary transformation,
      state.required).2 = state.required := rfl

/-- A minimal product of the epistemic loop and PettaClaw's life coordinate. -/
abbrev LivingAgent := State × Claws.Life

def updateEpistemic (change : State → State) (agent : LivingAgent) :
    LivingAgent :=
  (change agent.1, agent.2)

def updateLife (change : Claws.Life → Claws.Life) (agent : LivingAgent) :
    LivingAgent :=
  (agent.1, change agent.2)

/-- Epistemic receipt evolution and PettaClaw life evolution occupy independent
coordinates; neither loop needs to subsume the other. -/
theorem epistemic_and_life_steps_commute
    (agent : LivingAgent) (epistemic : State → State)
    (living : Claws.Life → Claws.Life) :
    updateLife living (updateEpistemic epistemic agent) =
      updateEpistemic epistemic (updateLife living agent) := rfl

/-- The attention lane supplies the orthogonal responsiveness condition: a
foreground human event blocks any requested autonomous burst. -/
theorem pending_attention_blocks_arbitrary_autonomy
    (state : ContextAttention.State)
    (event : ContextAttention.HumanEvent) (turns : Nat) :
    ContextAttention.autonomousRun turns
        { state with foreground := some event } =
      { state with foreground := some event } :=
  ContextAttention.foreground_blocks_autonomous_run state event turns

end AgentArchitecture

/-! ## Axiom audit -/
#print axioms AgentArchitecture.compaction_can_erase_view_but_not_log
#print axioms AgentArchitecture.heartbeat_can_be_process_live_without_cognition
#print axioms AgentArchitecture.model_turn_can_be_cognitively_live_without_verified_progress
#print axioms AgentArchitecture.claim_gate_prevents_silent_false_success
#print axioms AgentArchitecture.step_claim_requires_end_to_end_evidence
#print axioms AgentArchitecture.step_acceptance_requires_external_verification
#print axioms AgentArchitecture.LoopContract.no_silent_false_success
#print axioms AgentArchitecture.LoopContract.constraints_survive_and_are_visible
#print axioms AgentArchitecture.four_identical_observations_are_suspicious
#print axioms AgentArchitecture.epistemic_and_life_steps_commute
