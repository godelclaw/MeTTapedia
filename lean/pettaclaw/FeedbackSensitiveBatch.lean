import Mathlib

/-!
# Feedback-sensitive batches

This file isolates the smallest semantic distinction needed to combine coding
workflows with interactive agency.

A precommitted batch may contain several effects when every later choice is
independent of the observations produced by earlier effects.  It is not an
adequate implementation of a feedback-sensitive workflow: if two possible
observations require different continuations, one continuation chosen before
either observation is known must be wrong for at least one of them.

The result does not forbid batching.  It characterizes its boundary.  The
runner may batch an observation-invariant region, while an observation-producing
boundary returns control to the policy before the next dependent effect.
-/

namespace PettaClaw.FeedbackSensitiveBatch

/-- The continuation which would be correct after each possible observation. -/
abbrev RequiredContinuation (Observation Continuation : Type*) :=
  Observation → Continuation

/-- A workflow is feedback-sensitive when two possible observations require
different continuations. -/
def FeedbackSensitive {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation) : Prop :=
  ∃ first second, required first ≠ required second

/-- A precommitted continuation is correct only if the same choice is correct
for every observation which the preceding effect may produce. -/
def PrecommitmentCorrect {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation)
    (fixed : Continuation) : Prop :=
  ∀ observation, fixed = required observation

/-- No fixed continuation can correctly implement a feedback-sensitive step.
This is the elementary no-go theorem behind interactive batch failures. -/
theorem no_precommitted_continuation_for_feedback_sensitive_step
    {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation)
    (sensitive : FeedbackSensitive required) :
    ¬ ∃ fixed, PrecommitmentCorrect required fixed := by
  rintro ⟨fixed, correct⟩
  obtain ⟨first, second, differ⟩ := sensitive
  apply differ
  exact (correct first).symm.trans (correct second)

/-- Observation-invariance is exactly the condition under which a fixed
continuation can be adequate. -/
def ObservationInvariant {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation) : Prop :=
  ∀ first second, required first = required second

theorem precommitment_exists_iff_observation_invariant
    {Observation Continuation : Type*} [Inhabited Observation]
    (required : RequiredContinuation Observation Continuation) :
    (∃ fixed, PrecommitmentCorrect required fixed) ↔
      ObservationInvariant required := by
  constructor
  · rintro ⟨fixed, correct⟩ first second
    exact (correct first).symm.trans (correct second)
  · intro invariant
    exact ⟨required default, fun observation => invariant default observation⟩

/-- Returning the observation to the policy before choosing the continuation
implements every such requirement directly. -/
def observeThenChoose {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation)
    (observation : Observation) : Continuation :=
  required observation

theorem observe_then_choose_is_correct
    {Observation Continuation : Type*}
    (required : RequiredContinuation Observation Continuation)
    (observation : Observation) :
    observeThenChoose required observation = required observation := by
  rfl

/-! ## A concrete terminal-dialog witness -/

inductive Screen where
  | trustPrompt
  | serverSelection
  | idleShell
deriving Repr, DecidableEq, Inhabited

inductive NextEffect where
  | confirm
  | changeSelection
  | typeCommand
deriving Repr, DecidableEq

def requiredForScreen : RequiredContinuation Screen NextEffect
  | .trustPrompt => .confirm
  | .serverSelection => .changeSelection
  | .idleShell => .typeCommand

theorem terminal_dialog_is_feedback_sensitive :
    FeedbackSensitive requiredForScreen := by
  exact ⟨.trustPrompt, .serverSelection, by decide⟩

/-- A batch which observes a terminal and has already chosen its next key or
command cannot be correct for all reachable dialog states. -/
theorem fixed_terminal_followup_cannot_handle_every_screen :
    ¬ ∃ fixed, PrecommitmentCorrect requiredForScreen fixed :=
  no_precommitted_continuation_for_feedback_sensitive_step
    requiredForScreen terminal_dialog_is_feedback_sensitive

end PettaClaw.FeedbackSensitiveBatch

#print axioms PettaClaw.FeedbackSensitiveBatch.no_precommitted_continuation_for_feedback_sensitive_step
#print axioms PettaClaw.FeedbackSensitiveBatch.precommitment_exists_iff_observation_invariant
#print axioms PettaClaw.FeedbackSensitiveBatch.observe_then_choose_is_correct
#print axioms PettaClaw.FeedbackSensitiveBatch.fixed_terminal_followup_cannot_handle_every_screen
