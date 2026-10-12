import Mettapedia.GSLT.Dynamics.ScriptedBackup

/-!
# Boundary input observations do not recover component activity

Direct execution and a checked recorded player inhabit one independently
formed transition system. Every input word has the same boundary readout
from the corresponding valid initial states. Along a recorded input the
actual activity readout distinguishes evaluation from a table read.

Thus component activity does not factor through complete boundary input
behaviour. This compares the declared abstract operations; it does not
identify arbitrary internal interventions with external input probes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.BoundaryObservationDisclosure

open Mettapedia.GSLT.ScriptedBackup Mettapedia.GSLT.PrivilegedView
open Mettapedia.GSLT.Core.NonFactorization

universe u v w

variable {State : Type u} {Input : Type v} [DecidableEq Input]

abbrev Implementation (State : Type u) (Input : Type v) := Sum State (Player State Input)

def transition (step : State → Input → State) :
    Implementation State Input → Input → Implementation State Input
  | .inl state, input => .inl (step state input)
  | .inr player, input => .inr (backupStep step player input)

def surface {Output : Type w} (observe : State → Output) : Implementation State Input → Output
  | .inl state => observe state
  | .inr player => observe player.current

def componentActivity (step : State → Input → State) :
    Implementation State Input → Input → Activity
  | .inl _, _ => .evaluate
  | .inr player, input => (advance step player input).2

theorem direct_run (step : State → Input → State) (inputs : List Input) (state : State) :
    inputs.foldl (transition step) (.inl state) = .inl (inputs.foldl step state) := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest inductionHypothesis => exact inductionHypothesis _

theorem backup_run (step : State → Input → State) (inputs : List Input)
    (player : Player State Input) :
    inputs.foldl (transition step) (.inr player) =
      .inr (inputs.foldl (backupStep step) player) := by
  induction inputs generalizing player with
  | nil => rfl
  | cons input rest inductionHypothesis => exact inductionHypothesis _

theorem boundary_agreement (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (player : Player State Input) (valid : Coherent step player) :
    wordBehaviour (transition step) (surface observe) (.inl player.current) =
      wordBehaviour (transition step) (surface observe) (.inr player) := by
  funext inputs
  unfold wordBehaviour
  rw [direct_run, backup_run]
  exact (congrArg observe (run_current step inputs valid)).symm

def recordedPlayer (step : State → Input → State) (state : State) (inputs : List Input) :
    Player State Input := ⟨state, record step state inputs, false⟩

omit [DecidableEq Input] in
theorem recorded_coherent (step : State → Input → State) (state : State) (inputs : List Input) :
    Coherent step (recordedPlayer step state inputs) := fun _ => record_valid step state inputs

theorem recorded_boundary_agreement (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (inputs : List Input) :
    wordBehaviour (transition step) (surface observe) (.inl state) =
      wordBehaviour (transition step) (surface observe) (.inr (recordedPlayer step state inputs)) :=
  boundary_agreement step observe _ (recorded_coherent step state inputs)

theorem recorded_activity_separates (step : State → Input → State)
    (state : State) (input : Input) :
    componentActivity step (.inl state) input ≠
      componentActivity step (.inr (recordedPlayer step state [input])) input := by
  simp only [componentActivity, recordedPlayer, record, advance, Bool.false_eq_true,
    ↓reduceIte]
  decide

def activitySeparator (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (input : Input) :
    NonTrivialFiber (wordBehaviour (transition step) (surface observe)) (componentActivity step) where
  left := .inl state
  right := .inr (recordedPlayer step state [input])
  sameShadow := recorded_boundary_agreement step observe state [input]
  differentValue := fun same => recorded_activity_separates step state input (congrFun same input)

theorem boundary_does_not_recover_activity (step : State → Input → State) {Output : Type w}
    (observe : State → Output) (state : State) (input : Input) :
    ¬ Factors (wordBehaviour (transition step) (surface observe)) (componentActivity step) :=
  (activitySeparator step observe state input).not_factors

theorem actual_bool_control :
    wordBehaviour (transition Controls.write) (surface id) (.inl false) =
      wordBehaviour (transition Controls.write) (surface id)
        (.inr (recordedPlayer Controls.write false [false])) ∧
    componentActivity Controls.write (.inl false) false = .evaluate ∧
    componentActivity Controls.write
      (.inr (recordedPlayer Controls.write false [false])) false = .tableRead := by
  exact ⟨recorded_boundary_agreement _ _ _ _, rfl, rfl⟩

end Mettapedia.GSLT.BoundaryObservationDisclosure
