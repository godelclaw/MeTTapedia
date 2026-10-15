import Mettapedia.CognitiveArchitecture.Agent.ContextEpoch
import Mettapedia.CognitiveArchitecture.Agent.ContextAttention
import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection
import Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference
import Mettapedia.CognitiveArchitecture.GodelClaw.ToolBroker
import Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators

/-!
# Receipt-bearing recurrent workspace for the shared agent contracts

The state, epochs, result receipts and effect broker are the existing
architecture-neutral imports from GodelClaw. This application connects them
to a single published workspace slot and arbitrarily many named specialists.
Specialist observations remain distinct from executable permission.

Public motivation: Kanai, *A Control-Theoretic Formulation of Global Workspace
Theory* (2026), https://arxiv.org/abs/2608.15926 . Receiving and sending must
meet through the same internal mechanism. The split-route control below has
both operations but does not mediate information between specialists.

The discrete intervention contracts are not the paper's linear Hankel
operator, mediation index, or a criterion for phenomenal consciousness. No
runtime adequacy claim is made: these are executable shared Lean contracts
for a future adapter, with explicit observations and effect boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace

open Mettapedia.CognitiveArchitecture.Agent.WorldState
open Mettapedia.CognitiveArchitecture.Agent
open Mettapedia.CognitiveArchitecture.Consciousness
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.PredicateInvariance
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes


abbrev Context (Workspace : Type) := ContextEpoch.Epoch Workspace Nat Nat Nat EffectReceiptProjection.History
abbrev Delivery (Workspace : Type) := ContextEpoch.Request (Context Workspace) EffectReceiptProjection.History
abbrev Publication (Workspace : Type) :=
  ContextEpoch.Request (Context Workspace) (Context Workspace)

/-- Operational proposals and host effects, evidence deliveries, selected
specialist, complete context epoch, and read/execute capabilities are separate
coordinates of the existing agent product. -/
abbrev State (Workspace Specialist : Type) :=
  AgentState ((Specialist → EffectReceiptProjection.History) × EffectBrokerNoninterference.Runtime)
    (Specialist → Option (Delivery Workspace)) Specialist (Context Workspace)
    (ArchitecturalIndicators.Mode × (Specialist → Bool))

inductive Command (Workspace Specialist : Type) where
  | receive (specialist : Specialist) (history : EffectReceiptProjection.History)
  | select (specialist : Specialist)
  | ignite
  | consume (specialist : Specialist)
  | publish (request : Publication Workspace)
  /-- An experimental intervention, distinct from an ordinary publication. -/
  | overwrite (history : EffectReceiptProjection.History)

inductive Action (Workspace Specialist : Type) where
  | workspace (command : Command Workspace Specialist)
  | dispatch (specialist : Specialist)

variable {Workspace Specialist : Type}
  [DecidableEq Workspace] [DecidableEq Specialist]

/-- A connected reader uses the published slot. The decoy uses an unrelated
private proposal even though its receive and publish operations still work. -/
def reading (state : State Workspace Specialist) (specialist : Specialist) : EffectReceiptProjection.History :=
  match state.capabilities.1 with
  | .connected => state.context.view
  | .shadow => state.operational.1 specialist

def step (state : State Workspace Specialist) : Command Workspace Specialist →
    State Workspace Specialist
  | .receive specialist history =>
      { state with operational :=
          (Function.update state.operational.1 specialist history, state.operational.2) }
  | .select specialist => { state with commitments := specialist }
  | .ignite =>
      let candidate := { state.context with view := state.operational.1 state.commitments }
      let context := ContextEpoch.publish state.context (ContextEpoch.prepare state.context candidate)
      { state with context := context }
  | .consume specialist =>
      let history := reading state specialist
      { state with
        operational :=
          (Function.update state.operational.1 specialist history, state.operational.2)
        evidence := Function.update state.evidence specialist
          (some (ContextEpoch.prepare state.context history)) }
  | .publish request => { state with context := ContextEpoch.publish state.context request }
  | .overwrite history =>
      { state with context := { state.context with view := history } }

def run (state : State Workspace Specialist) (commands : List (Command Workspace Specialist)) :
    State Workspace Specialist := commands.foldl step state

/-- Only the explicit effect action reaches the existing broker. Its admission
bit is read from capabilities, never from a workspace proposal or receipt. -/
def actionStep (state : State Workspace Specialist) : Action Workspace Specialist →
    State Workspace Specialist
  | .workspace command => step state command
  | .dispatch specialist =>
      { state with operational :=
          (state.operational.1,
            EffectBrokerNoninterference.broker (state.capabilities.2 specialist)
              (state.operational.1 specialist).proposal state.operational.2) }

def actionRun (state : State Workspace Specialist)
    (actions : List (Action Workspace Specialist)) : State Workspace Specialist :=
  actions.foldl actionStep state

@[simp] theorem step_effects (state : State Workspace Specialist)
    (command : Command Workspace Specialist) :
    (step state command).operational.2 = state.operational.2 := by
  cases command <;> rfl

@[simp] theorem step_capabilities (state : State Workspace Specialist)
    (command : Command Workspace Specialist) :
    (step state command).capabilities = state.capabilities := by
  cases command <;> rfl

theorem workspace_words_do_not_execute (state : State Workspace Specialist)
    (commands : List (Command Workspace Specialist)) :
    (run state commands).operational.2 = state.operational.2 := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact (inductionHypothesis (step state command)).trans (step_effects state command)

theorem workspace_words_do_not_grant_permission (state : State Workspace Specialist)
    (commands : List (Command Workspace Specialist)) :
    (run state commands).capabilities = state.capabilities := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact (inductionHypothesis (step state command)).trans (step_capabilities state command)

omit [DecidableEq Workspace] in
theorem withheld_dispatch_stutters [DecidableEq Workspace] (state : State Workspace Specialist)
    (specialist : Specialist) (withheld : state.capabilities.2 specialist = false) :
    actionStep state (.dispatch specialist) = state := by
  cases state
  simp_all [actionStep, EffectBrokerNoninterference.broker]

omit [DecidableEq Workspace] in
theorem admitted_dispatch_records_effect [DecidableEq Workspace] (state : State Workspace Specialist)
    (specialist : Specialist) (admitted : state.capabilities.2 specialist = true) :
    (actionStep state (.dispatch specialist)).operational.2.effects =
      state.operational.2.effects ++ [(state.operational.1 specialist).proposal] := by
  simp [actionStep, EffectBrokerNoninterference.broker, admitted, EffectBrokerNoninterference.perform]

/-- Populate one permission from the existing tool gate, rather than deriving
execution permission from the content that a specialist reads. -/
def withToolPolicy (state : State Workspace Specialist) (specialist : Specialist)
    (isBrokered shadowsNative inAllowlist wildcard : Bool) : State Workspace Specialist :=
  { state with capabilities :=
      (state.capabilities.1, Function.update state.capabilities.2 specialist
        (ToolBroker.toolGateAllows isBrokered shadowsNative inAllowlist wildcard)) }

theorem workspace_cannot_bypass_tool_denial (state : State Workspace Specialist)
    (specialist : Specialist) (commands : List (Command Workspace Specialist))
    (isBrokered shadowsNative inAllowlist wildcard : Bool)
    (denied : ToolBroker.toolGateAllows isBrokered shadowsNative inAllowlist wildcard = false) :
    let after := run (withToolPolicy state specialist
      isBrokered shadowsNative inAllowlist wildcard) commands
    actionStep after (.dispatch specialist) = after := by
  dsimp
  apply withheld_dispatch_stutters
  rw [workspace_words_do_not_grant_permission]
  simpa [withToolPolicy] using denied

/-! ## Mediation and feedback at the actual receipt-bearing slot -/

def broadcastWord (source target : Specialist) (history : EffectReceiptProjection.History) :
    List (Command Workspace Specialist) :=
  [.receive source history, .select source, .ignite, .consume target]

def feedbackWord (specialist : Specialist) (history erased : EffectReceiptProjection.History) :
    List (Command Workspace Specialist) :=
  [.overwrite history, .consume specialist, .overwrite erased, .select specialist, .ignite]

/-- A report is linked to the published epoch only when it retains that epoch
and the payload actually comes from its view. -/
def CurrentDelivery (state : State Workspace Specialist) (specialist : Specialist) : Prop :=
  ∃ delivery, state.evidence specialist = some delivery ∧
    delivery.Current state.context ∧ delivery.payload = state.context.view

def ReportsCompleted (state : State Workspace Specialist) (specialist : Specialist) : Prop :=
  ∃ delivery, state.evidence specialist = some delivery ∧
    delivery.Current state.context ∧ delivery.payload = state.context.view ∧
    EffectReceiptProjection.Completed delivery.payload

theorem connected_consume_links_epoch (state : State Workspace Specialist)
    (specialist : Specialist) (connected : state.capabilities.1 = .connected) :
    CurrentDelivery (step state (.consume specialist)) specialist := by
  exact ⟨ContextEpoch.prepare state.context state.context.view,
    by simp [step, reading, connected], rfl, rfl⟩

theorem connected_completion_iff (state : State Workspace Specialist)
    (specialist : Specialist) (connected : state.capabilities.1 = .connected) :
    ReportsCompleted (step state (.consume specialist)) specialist ↔
      EffectReceiptProjection.Completed state.context.view := by
  simp [ReportsCompleted, step, reading, connected, ContextEpoch.Request.Current, ContextEpoch.prepare]

/-- The same exact history received from one specialist is delivered to any
other specialist through the selected and published workspace. -/
theorem connected_broadcast (state : State Workspace Specialist)
    (source target : Specialist) (history : EffectReceiptProjection.History)
    (connected : state.capabilities.1 = .connected) :
    (run state (broadcastWord source target history)).evidence target =
      some (ContextEpoch.prepare
        { state.context with sequence := state.context.sequence + 1, view := history }
        history) := by
  simp [run, broadcastWord, step, reading, connected]

theorem connected_broadcast_proposal (state : State Workspace Specialist)
    (source target : Specialist) (history : EffectReceiptProjection.History)
    (connected : state.capabilities.1 = .connected) :
    (run state (broadcastWord source target history)).operational.1 target = history := by
  simp [run, broadcastWord, step, reading, connected]

/-- Erasing the slot before re-ignition ensures this tests a recurrent path
through a specialist, rather than persistence of the original publication. -/
theorem connected_feedback_after_erasure (state : State Workspace Specialist)
    (specialist : Specialist) (history erased : EffectReceiptProjection.History)
    (connected : state.capabilities.1 = .connected) :
    (run state (feedbackWord specialist history erased)).context.view = history := by
  simp [run, feedbackWord, step, reading, connected]

theorem broadcast_completion_iff (state : State Workspace Specialist)
    (source target : Specialist) (history : EffectReceiptProjection.History)
    (connected : state.capabilities.1 = .connected) :
    ReportsCompleted (run state (broadcastWord source target history)) target ↔
      EffectReceiptProjection.Completed history := by
  have context : (run state (broadcastWord source target history)).context =
      { state.context with sequence := state.context.sequence + 1, view := history } := by
    simp [run, broadcastWord, step]
  simp [ReportsCompleted, connected_broadcast state source target history connected,
    context, ContextEpoch.Request.Current, ContextEpoch.prepare]

/-- The split route still receives and publishes the new history, but its
different reader returns its private history instead of the publication. -/
theorem split_route_does_not_mediate (state : State Workspace Specialist)
    (source target : Specialist) (different : source ≠ target)
    (history : EffectReceiptProjection.History) (split : state.capabilities.1 = .shadow) :
    (run state (broadcastWord source target history)).context.view = history ∧
      (run state (broadcastWord source target history)).evidence target =
        some (ContextEpoch.prepare
          { state.context with sequence := state.context.sequence + 1, view := history }
          (state.operational.1 target)) := by
  simp [run, broadcastWord, step, reading, split, Ne.symm different]

theorem split_new_content_is_not_linked (state : State Workspace Specialist)
    (source target : Specialist) (different : source ≠ target)
    (history : EffectReceiptProjection.History) (changed : state.operational.1 target ≠ history)
    (split : state.capabilities.1 = .shadow) :
    ¬ CurrentDelivery (run state (broadcastWord source target history)) target := by
  obtain ⟨workspace, report⟩ :=
    split_route_does_not_mediate state source target different history split
  simp [CurrentDelivery, report, workspace, ContextEpoch.prepare, changed]

/-! ## Freshness of asynchronous publication and retained deliveries -/

theorem stale_publication_preserves_all_layers (state : State Workspace Specialist)
    (request : Publication Workspace) (stale : state.context ≠ request.epoch) :
    step state (.publish request) = state := by
  cases state
  simp_all [step, ContextEpoch.publish_stale]

theorem sibling_publication_cannot_overwrite (state : State Workspace Specialist)
    (first second : Context Workspace) :
    step (step state (.publish (ContextEpoch.prepare state.context first)))
        (.publish (ContextEpoch.prepare state.context second)) =
      step state (.publish (ContextEpoch.prepare state.context first)) := by
  simp only [step, ContextEpoch.publication_invalidates_sibling]

theorem consume_then_publish_retains_stale_receipt (state : State Workspace Specialist)
    (specialist : Specialist) (next : Context Workspace)
    (connected : state.capabilities.1 = .connected) :
    let after := step (step state (.consume specialist))
      (.publish (ContextEpoch.prepare state.context next))
    after.evidence specialist = some (ContextEpoch.prepare state.context state.context.view) ∧
      ¬ CurrentDelivery after specialist := by
  dsimp
  constructor
  · simp [step, reading, connected]
  · rintro ⟨delivery, received, current, _⟩
    have deliveryEq : delivery = ContextEpoch.prepare state.context state.context.view := by
      simpa [step, reading, connected] using received.symm
    subst delivery
    exact ContextEpoch.old_consumer_request_is_not_current state.context next
      state.context.view current

/-! ## The imported attention lane controls the workspace

The control lane is not another specialist. It gates autonomous transitions
before they reach the workspace or effect broker. Acknowledgements retain the
complete context epoch, so a value-equal later event cannot reuse an earlier
acknowledgement.
-/

abbrev ControlledState (Workspace Specialist : Type) :=
  State Workspace Specialist × ContextAttention.State

def Ready (control : ContextAttention.State) : Prop :=
  control.halted = false ∧ control.foreground = none ∧ control.inbox = []

def controlledTick (state : ControlledState Workspace Specialist)
    (action : Action Workspace Specialist) : ControlledState Workspace Specialist :=
  let next := ContextAttention.autonomousStep state.2
  if next = state.2 then state else (actionStep state.1 action, next)

def controlledRun (state : ControlledState Workspace Specialist)
    (actions : List (Action Workspace Specialist)) : ControlledState Workspace Specialist :=
  actions.foldl controlledTick state

theorem ready_step_remains_ready (control : ContextAttention.State) (ready : Ready control) :
    Ready (ContextAttention.autonomousStep control) := by
  rcases ready with ⟨running, foreground, inbox⟩
  simp [Ready, ContextAttention.autonomousStep, running, foreground, inbox]

theorem ready_step_advances (control : ContextAttention.State) (ready : Ready control) :
    ContextAttention.autonomousStep control ≠ control := by
  rcases ready with ⟨running, foreground, inbox⟩
  intro same
  have turns := congrArg ContextAttention.State.autonomousTurns same
  simp [ContextAttention.autonomousStep, running, foreground, inbox] at turns

theorem controlledTick_ready (state : ControlledState Workspace Specialist)
    (action : Action Workspace Specialist) (ready : Ready state.2) :
    controlledTick state action =
      (actionStep state.1 action, ContextAttention.autonomousStep state.2) := by
  simp [controlledTick, ready_step_advances state.2 ready]

/-- The control adapter preserves the actual inner run when no human input is
pending. It is productive, rather than a controller that always blocks. -/
theorem controlledRun_ready (state : ControlledState Workspace Specialist)
    (actions : List (Action Workspace Specialist)) (ready : Ready state.2) :
    controlledRun state actions =
      (actionRun state.1 actions,
        ContextAttention.autonomousRun actions.length state.2) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions inductionHypothesis =>
      change controlledRun (controlledTick state action) actions = _
      rw [controlledTick_ready state action ready]
      rw [inductionHypothesis _ (ready_step_remains_ready state.2 ready)]
      rfl

theorem control_stutter_blocks_all_actions (state : ControlledState Workspace Specialist)
    (blocked : ContextAttention.autonomousStep state.2 = state.2)
    (actions : List (Action Workspace Specialist)) : controlledRun state actions = state := by
  induction actions with
  | nil => rfl
  | cons action actions inductionHypothesis =>
      change controlledRun (controlledTick state action) actions = state
      simpa [controlledTick, blocked] using inductionHypothesis

theorem pending_human_input_blocks_workspace_and_effects
    (state : ControlledState Workspace Specialist) (event : ContextAttention.HumanEvent)
    (pending : state.2.foreground = some event)
    (actions : List (Action Workspace Specialist)) : controlledRun state actions = state := by
  apply control_stutter_blocks_all_actions
  simp [ContextAttention.autonomousStep, pending]

def receiveHuman (state : ControlledState Workspace Specialist)
    (event : ContextAttention.HumanEvent) : ControlledState Workspace Specialist :=
  let context := ContextEpoch.publish state.1.context
    (ContextEpoch.prepare state.1.context state.1.context)
  ({ state.1 with context := context }, ContextAttention.receive state.2 event)

def acknowledgeHuman (state : ControlledState Workspace Specialist)
    (request : ContextEpoch.Request (Context Workspace) ContextAttention.HumanEvent) :
    ControlledState Workspace Specialist :=
  if request.epoch = state.1.context then
    let next := ContextAttention.acknowledge state.2 request.payload
    if next = state.2 then state else
      let context := ContextEpoch.publish state.1.context
        (ContextEpoch.prepare state.1.context state.1.context)
      ({ state.1 with context := context }, next)
  else state

theorem stop_blocks_arbitrary_workspace_run (state : ControlledState Workspace Specialist)
    (actions : List (Action Workspace Specialist)) :
    controlledRun (receiveHuman state .stop) actions = receiveHuman state .stop := by
  apply control_stutter_blocks_all_actions
  simp [receiveHuman, ContextAttention.receive, ContextAttention.autonomousStep]

omit [DecidableEq Specialist] in
theorem stale_acknowledgement_stutters (state : ControlledState Workspace Specialist)
    (request : ContextEpoch.Request (Context Workspace) ContextAttention.HumanEvent)
    (stale : request.epoch ≠ state.1.context) : acknowledgeHuman state request = state := by
  simp [acknowledgeHuman, stale]

omit [DecidableEq Specialist] in
/-- Receiving a fresh event invalidates every acknowledgement prepared at the
previous context, even if the event value is identical. -/
theorem fresh_event_rejects_old_acknowledgement
    (state : ControlledState Workspace Specialist) (event receipt : ContextAttention.HumanEvent) :
    acknowledgeHuman (receiveHuman state event)
        (ContextEpoch.prepare state.1.context receipt) = receiveHuman state event := by
  apply stale_acknowledgement_stutters
  exact ContextEpoch.old_consumer_request_is_not_current state.1.context
    state.1.context receipt

omit [DecidableEq Specialist] in
theorem accepted_acknowledgement_cannot_replay
    (state : ControlledState Workspace Specialist) (receipt : ContextAttention.HumanEvent)
    (changes : ContextAttention.acknowledge state.2 receipt ≠ state.2) :
    let request := ContextEpoch.prepare state.1.context receipt
    acknowledgeHuman (acknowledgeHuman state request) request =
      acknowledgeHuman state request := by
  dsimp
  apply stale_acknowledgement_stutters
  unfold acknowledgeHuman
  rw [if_pos (show (ContextEpoch.prepare state.1.context receipt).epoch =
    state.1.context from rfl)]
  dsimp only
  rw [if_neg (show ContextAttention.acknowledge state.2
    (ContextEpoch.prepare state.1.context receipt).payload ≠ state.2 from changes)]
  exact ContextEpoch.old_consumer_request_is_not_current state.1.context
    state.1.context receipt

omit [DecidableEq Specialist] in
theorem control_observation_does_not_execute (state : ControlledState Workspace Specialist)
    (event : ContextAttention.HumanEvent)
    (request : ContextEpoch.Request (Context Workspace) ContextAttention.HumanEvent) :
    (receiveHuman state event).1.operational.2 = state.1.operational.2 ∧
      (acknowledgeHuman state request).1.operational.2 = state.1.operational.2 := by
  constructor
  · rfl
  · unfold acknowledgeHuman
    split
    · dsimp only
      split <;> rfl
    · rfl

/-! ## Query-relative compression of diagnostic evidence -/

inductive Diagnostic (Specialist : Type) where
  | current (specialist : Specialist)
  | completed (specialist : Specialist)

def diagnosticAnswer (state : State Workspace Specialist) : Diagnostic Specialist → Prop
  | .current specialist => CurrentDelivery state specialist
  | .completed specialist => ReportsCompleted state specialist

def diagnosticView (state : State Workspace Specialist) := (state.context, state.evidence)

omit [DecidableEq Workspace] [DecidableEq Specialist] in
theorem diagnosticView_queryComplete : QueryComplete
    (diagnosticAnswer (Workspace := Workspace) (Specialist := Specialist)) diagnosticView := by
  refine ⟨fun view query => match query with
    | .current specialist => ∃ delivery, view.2 specialist = some delivery ∧
        delivery.Current view.1 ∧ delivery.payload = view.1.view
    | .completed specialist => ∃ delivery, view.2 specialist = some delivery ∧
        delivery.Current view.1 ∧ delivery.payload = view.1.view ∧
        EffectReceiptProjection.Completed delivery.payload, ?_⟩
  intro state query
  cases query <;> rfl

/-! ## The existing GSLT and OSLF interfaces -/

def theory (Workspace Specialist : Type) [DecidableEq Workspace] [DecidableEq Specialist] : GSLT :=
  equalityGSLT (State Workspace Specialist)
    (fun source target => ∃ action, actionStep source action = target)

inductive Atom (Specialist : Type) where
  | workspace (history : EffectReceiptProjection.History)
  | current (specialist : Specialist)
  | completed (specialist : Specialist)
  | effects (commands : List EffectBrokerNoninterference.Command)

def observes (atom : Atom Specialist) (state : State Workspace Specialist) : Prop :=
  match atom with
  | .workspace history => state.context.view = history
  | .current specialist => CurrentDelivery state specialist
  | .completed specialist => ReportsCompleted state specialist
  | .effects commands => state.operational.2.effects = commands

def modal : System (theory Workspace Specialist) where
  Atom := Atom Specialist
  observes := observes
  observes_resp := by intro atom left right same; cases same; rfl
  Label := Action Workspace Specialist
  act action source target := actionStep source action = target
  act_resp_left := by
    intro action source other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  act_resp_right := by
    intro action source target other advances same
    cases same
    exact advances

def probeFormula (actions : List (Action Workspace Specialist)) (atom : Atom Specialist) :
    Formula (Atom Specialist) (Action Workspace Specialist) :=
  Formula.after actions (.atom atom)

theorem probeFormula_exact (actions : List (Action Workspace Specialist))
    (atom : Atom Specialist) (state : State Workspace Specialist) :
    modal.sat (probeFormula actions atom) state ↔
      observes atom (actionRun state actions) := by
  exact modal.sat_after_deterministic actionStep (fun _ _ _ => Iff.rfl)
    actions (.atom atom) state

def probeNativeType (actions : List (Action Workspace Specialist)) (atom : Atom Specialist) :
    GSLTNativeType (theory Workspace Specialist) :=
  formulaNativeType modal (probeFormula actions atom)

theorem nativeProbe_exact (actions : List (Action Workspace Specialist))
    (atom : Atom Specialist) (state : State Workspace Specialist) :
    (gsltOSLF (theory Workspace Specialist)).satisfies (S := ()) state
        (probeNativeType actions atom).pred ↔
      observes atom (actionRun state actions) := probeFormula_exact actions atom state

/-- The same OSLF query describes the controlled execution when the imported
attention lane is ready. A blocked lane requires the controlled semantics. -/
theorem controlled_nativeProbe_exact (actions : List (Action Workspace Specialist))
    (atom : Atom Specialist) (state : ControlledState Workspace Specialist)
    (ready : Ready state.2) :
    (gsltOSLF (theory Workspace Specialist)).satisfies (S := ()) state.1
        (probeNativeType actions atom).pred ↔
      observes atom (controlledRun state actions).1 := by
  rw [controlledRun_ready state actions ready]
  exact nativeProbe_exact actions atom state.1

/-! ## Discriminating controls -/

namespace Controls

def context : Context Nat :=
  ⟨0, 41, 2, 3, 5, EffectReceiptProjection.returnedFailure⟩

def initial (mode : ArchitecturalIndicators.Mode) (permitted : Bool) : State Nat Bool :=
  ⟨(fun _ => EffectReceiptProjection.returnedFailure, ⟨[]⟩),
    fun _ => none, false, context, (mode, fun _ => permitted)⟩

theorem successful_receipt_is_broadcast_as_completed :
    ReportsCompleted
      (run (initial .connected false)
        (broadcastWord false true EffectReceiptProjection.successful)) true := by
  apply (broadcast_completion_iff (initial .connected false) false true
    EffectReceiptProjection.successful rfl).2
  rfl

theorem withheld_receipt_is_broadcast_without_completion :
    ¬ ReportsCompleted
      (run (initial .connected false)
        (broadcastWord false true EffectReceiptProjection.withheld)) true := by
  rw [broadcast_completion_iff _ _ _ _ rfl]
  exact EffectReceiptProjection.withheld_is_not_completed 7

theorem returned_failure_is_not_promoted_to_success :
    ¬ ReportsCompleted
      (run (initial .connected false)
        (broadcastWord false true EffectReceiptProjection.returnedFailure)) true := by
  rw [broadcast_completion_iff _ _ _ _ rfl]
  exact EffectReceiptProjection.returned_failure_is_not_completed 7

theorem split_receiver_and_sender_are_not_a_mediator :
    let after := run (initial .shadow false)
      (broadcastWord false true EffectReceiptProjection.successful)
    after.context.view = EffectReceiptProjection.successful ∧
      after.operational.1 false = EffectReceiptProjection.successful ∧
      ¬ CurrentDelivery after true := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact (split_route_does_not_mediate (initial .shadow false) false true
      (by decide) EffectReceiptProjection.successful rfl).1
  · simp [run, broadcastWord, step, reading, initial]
  · exact split_new_content_is_not_linked (initial .shadow false) false true
      (by decide) EffectReceiptProjection.successful (by decide) rfl

theorem broadcast_does_not_authorize_the_proposed_effect :
    let after := run (initial .connected false)
      (broadcastWord false true EffectReceiptProjection.successful)
    actionStep after (.dispatch true) = after ∧ after.operational.2.effects = [] := by
  dsimp
  constructor
  · apply withheld_dispatch_stutters
    exact congrArg (fun capabilities => capabilities.2 true)
      (workspace_words_do_not_grant_permission (initial .connected false)
        (broadcastWord false true EffectReceiptProjection.successful))
  · exact congrArg EffectBrokerNoninterference.Runtime.effects
      (workspace_words_do_not_execute _ _)

theorem admitted_broadcast_proposal_can_execute :
    let after := run (initial .connected true)
      (broadcastWord false true EffectReceiptProjection.successful)
    (actionStep after (.dispatch true)).operational.2.effects = [7] := by
  simp [actionStep, run, broadcastWord, step, reading, initial,
    EffectBrokerNoninterference.broker, EffectBrokerNoninterference.perform,
    EffectReceiptProjection.successful]

theorem same_sequence_changed_instructions_cannot_publish :
    let live := { context with instructionRevision := 99 }
    ContextEpoch.publish live (ContextEpoch.prepare context context) = live := by
  dsimp
  apply ContextEpoch.publish_stale
  intro same
  have impossible := congrArg ContextEpoch.Epoch.instructionRevision same
  contradiction

def fresh : State Nat Bool :=
  step { initial .connected false with
    context := { context with view := EffectReceiptProjection.successful } } (.consume true)

def stale : State Nat Bool :=
  step fresh (.publish (ContextEpoch.prepare fresh.context fresh.context))

theorem fresh_delivery_is_completed : ReportsCompleted fresh true := by
  apply (connected_completion_iff _ _ rfl).2
  rfl

theorem stale_delivery_is_not_current : ¬ CurrentDelivery stale true := by
  exact (consume_then_publish_retains_stale_receipt
    { initial .connected false with
      context := { context with view := EffectReceiptProjection.successful } }
    true fresh.context rfl).2

theorem same_payload_different_currency :
    fresh.context.view = stale.context.view ∧
      ReportsCompleted fresh true ∧ ¬ ReportsCompleted stale true := by
  refine ⟨?_, fresh_delivery_is_completed, ?_⟩
  · simp [fresh, stale, step]
  · rintro ⟨delivery, received, current, linked, _⟩
    exact stale_delivery_is_not_current ⟨delivery, received, current, linked⟩

/-- A content-only compression cannot answer even these two diagnostic
queries: identical payloads can have different completion currency. -/
theorem content_only_not_queryComplete :
    ¬ QueryComplete (diagnosticAnswer (Workspace := Nat) (Specialist := Bool))
      (fun state => state.context.view) := by
  rintro ⟨recover, recovers⟩
  have same := congrArg (fun view => recover view (.completed true))
    same_payload_different_currency.1
  rw [recovers, recovers] at same
  exact same_payload_different_currency.2.2 (Eq.mp same fresh_delivery_is_completed)

/-- The upstream event-value acknowledgement alone admits replay when an
identical message arrives again. The epoch-bound adapter rejects that replay. -/
theorem event_value_alone_allows_acknowledgement_replay :
    let event := ContextAttention.HumanEvent.message 1
    let first := ContextAttention.receive ContextAttention.initial event
    let handled := ContextAttention.acknowledge first event
    let second := ContextAttention.receive handled event
    second.foreground = some event ∧
      (ContextAttention.acknowledge second event).foreground = none := by
  decide

def waiting : ControlledState Nat Bool :=
  receiveHuman (initial .connected true, ContextAttention.initial) (.message 1)

def acknowledgement := ContextEpoch.prepare waiting.1.context
  (ContextAttention.HumanEvent.message 1)

theorem current_acknowledgement_clears_pending_event :
    (acknowledgeHuman waiting acknowledgement).2.foreground = none := by
  decide

theorem current_acknowledgement_advances_epoch :
    (acknowledgeHuman waiting acknowledgement).1.context.sequence =
      waiting.1.context.sequence + 1 := by
  decide

theorem accepted_acknowledgement_is_single_use :
    acknowledgeHuman (acknowledgeHuman waiting acknowledgement) acknowledgement =
      acknowledgeHuman waiting acknowledgement := by
  apply accepted_acknowledgement_cannot_replay
  decide

theorem identical_new_message_rejects_old_acknowledgement :
    let handled := acknowledgeHuman waiting acknowledgement
    let second := receiveHuman handled (.message 1)
    acknowledgeHuman second acknowledgement = second := by
  dsimp
  apply stale_acknowledgement_stutters
  intro same
  have impossible := congrArg ContextEpoch.Epoch.sequence same
  change 1 = 3 at impossible
  contradiction

end Controls

end Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace
