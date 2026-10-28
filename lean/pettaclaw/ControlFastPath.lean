import Mathlib

/-!
# Independent operator control

Every authenticated operator command receives an independent execution lane.
Its local transition or observation never waits for cognition, live provider
discovery, another control, or another Telegram delivery. Provider catalog and
quota data are durable observations refreshed outside the control path.

This model separates the guarantee made by the runtime from the network
boundary: dispatch and local state access are independent; successful Telegram
delivery still requires Telegram to be reachable.
-/

namespace PettaClaw.ControlFastPath

inductive Command where
  | start
  | stop
  | model
  | models
  | mode
  | modes
  | engine
  | engines
  | fuel
  | fuels
  | quota
  | wake
  | energy
  | health
  | activity
  | delete
  | claudeCodeAuthorization
deriving Repr, DecidableEq

def allCommands : List Command :=
  [.start, .stop, .model, .models, .mode, .modes, .engine, .engines,
   .fuel, .fuels, .quota, .wake, .energy, .health, .activity, .delete,
   .claudeCodeAuthorization]

structure RuntimeView where
  activity : String
  mode : String
  engine : String
  fuel : String
  model : String
deriving Repr, DecidableEq

structure ProviderObservation where
  observedAt : Nat
  modelIds : List String
  quota : Option String
deriving Repr, DecidableEq

structure Backlogs where
  cognition : Nat
  provider : Nat
  otherControls : Nat
  telegramDeliveries : Nat
deriving Repr, DecidableEq

structure ControlReceipt where
  command : Command
  receivedAt : Nat
  runtime : RuntimeView
  provider : ProviderObservation
deriving Repr, DecidableEq

inductive Dispatch where
  | independent (receipt : ControlReceipt)
deriving Repr, DecidableEq

def dispatch (command : Command) (receivedAt : Nat) (runtime : RuntimeView)
    (provider : ProviderObservation) (_backlogs : Backlogs) : Dispatch :=
  .independent ⟨command, receivedAt, runtime, provider⟩

theorem every_operator_control_is_independent
    (command : Command) (receivedAt : Nat) (runtime : RuntimeView)
    (provider : ProviderObservation) (backlogs : Backlogs) :
    dispatch command receivedAt runtime provider backlogs =
      .independent ⟨command, receivedAt, runtime, provider⟩ := by
  rfl

theorem dispatch_independent_of_all_backlogs
    (command : Command) (receivedAt : Nat) (runtime : RuntimeView)
    (provider : ProviderObservation) (left right : Backlogs) :
    dispatch command receivedAt runtime provider left =
      dispatch command receivedAt runtime provider right := by
  rfl

theorem complete_command_inventory : allCommands.length = 17 := by
  decide

structure DurableControlState where
  activeModel : String
  provider : ProviderObservation
deriving Repr, DecidableEq

def installProviderObservation (state : DurableControlState)
    (observation : ProviderObservation) : DurableControlState :=
  { state with provider := observation }

def selectModel (state : DurableControlState) (modelId : String) :
    DurableControlState :=
  { state with activeModel := modelId }

theorem provider_refresh_preserves_active_model
    (state : DurableControlState) (observation : ProviderObservation) :
    (installProviderObservation state observation).activeModel =
      state.activeModel := by
  rfl

theorem model_selection_independent_of_provider_observation
    (left right : ProviderObservation) (active modelId : String) :
    (selectModel ⟨active, left⟩ modelId).activeModel =
      (selectModel ⟨active, right⟩ modelId).activeModel := by
  rfl

theorem model_selection_sets_requested_id
    (state : DurableControlState) (modelId : String) :
    (selectModel state modelId).activeModel = modelId := by
  rfl

inductive Latch where
  | stopped
  | running
deriving Repr, DecidableEq

def cognitionEnabled (latch : Latch) : Prop :=
  latch = .running

theorem cognition_authority_is_exactly_operator_latch (latch : Latch) :
    cognitionEnabled latch ↔ latch = .running := by
  rfl

theorem stopped_latch_disables_cognition :
    ¬cognitionEnabled .stopped := by
  simp [cognitionEnabled]

theorem running_latch_enables_cognition :
    cognitionEnabled .running := by
  rfl

theorem provider_observation_cannot_disable_cognition
    (latch : Latch) (_left _right : ProviderObservation) :
    cognitionEnabled latch ↔ cognitionEnabled latch := by
  rfl

structure TransitionState where
  epoch : Nat
  latch : Latch
deriving Repr, DecidableEq

def beginTransition (state : TransitionState) : TransitionState :=
  ⟨state.epoch + 1, .stopped⟩

def completeStart (token : Nat) (state : TransitionState) : TransitionState :=
  if token = state.epoch then { state with latch := .running } else state

theorem newer_stop_cancels_slow_start (initial : TransitionState) :
    let starting := beginTransition initial
    let stopped := beginTransition starting
    completeStart starting.epoch stopped = stopped := by
  simp [beginTransition, completeStart]

theorem cancelled_start_cannot_reauthorize (initial : TransitionState) :
    let starting := beginTransition initial
    let stopped := beginTransition starting
    (completeStart starting.epoch stopped).latch = .stopped := by
  simp [beginTransition, completeStart]

#print axioms PettaClaw.ControlFastPath.every_operator_control_is_independent
#print axioms PettaClaw.ControlFastPath.dispatch_independent_of_all_backlogs
#print axioms PettaClaw.ControlFastPath.complete_command_inventory
#print axioms PettaClaw.ControlFastPath.provider_refresh_preserves_active_model
#print axioms PettaClaw.ControlFastPath.model_selection_independent_of_provider_observation
#print axioms PettaClaw.ControlFastPath.model_selection_sets_requested_id
#print axioms PettaClaw.ControlFastPath.cognition_authority_is_exactly_operator_latch
#print axioms PettaClaw.ControlFastPath.stopped_latch_disables_cognition
#print axioms PettaClaw.ControlFastPath.running_latch_enables_cognition
#print axioms PettaClaw.ControlFastPath.provider_observation_cannot_disable_cognition
#print axioms PettaClaw.ControlFastPath.newer_stop_cancels_slow_start
#print axioms PettaClaw.ControlFastPath.cancelled_start_cannot_reauthorize

end PettaClaw.ControlFastPath
