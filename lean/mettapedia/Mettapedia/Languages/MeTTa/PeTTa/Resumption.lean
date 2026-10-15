import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Pausing and resuming the retained PeTTa configuration machine

The residual is the existing configuration, including bindings in its control
and frames, private store, pending alternatives, input and output. A completed
observation and a primitive fault are terminal; only exhaustion is resumable.
The budget counts source-machine transitions. It is not a bound on the cost
of a primitive operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)

/-- Resume only a retained residual. Terminal outcomes remain terminal. -/
def resume (program : Program) (fuel : Nat) : Outcome → Outcome
  | .exhausted configuration => run program fuel configuration
  | outcome => outcome

@[simp] private theorem run_returned (program : Program) (fuel : Nat)
    (state : Effects.State) (answers input output : List Atom) :
    run program fuel { state, control := .returned answers, input, output } =
      .complete state answers input output := by
  cases fuel <;> rfl

@[simp] private theorem run_faulted (program : Program) (fuel : Nat)
    (state : Effects.State) (reason : Effects.Fault) (frames : List Frame)
    (input output : List Atom) :
    run program fuel { state, control := .fault reason, frames, input, output } =
      .fault reason { state, control := .fault reason, frames, input, output } := by
  cases fuel <;> rfl

/-- Splitting an execution budget preserves the complete observation, not
just its answer support. No primitive or effect is replayed at resumption. -/
theorem resume_run (program : Program) (first second : Nat)
    (configuration : Configuration) :
    resume program second (run program first configuration) =
      run program (first + second) configuration := by
  induction first generalizing configuration with
  | zero =>
      cases configuration with
      | mk state control frames input output =>
          cases control <;> cases frames
          all_goals simp only [run]
          all_goals simp [resume]
  | succ first ih =>
      cases configuration with
      | mk state control frames input output =>
          cases control <;> cases frames
          all_goals rw [show first + 1 + second = (first + second) + 1 by omega]
          all_goals simp only [run]
          all_goals try solve | simp [resume]
          all_goals split
          all_goals
            first
            | simpa [Nat.add_right_comm] using ih _
            | cases second <;> simp_all only [resume, run]

/-- An exhausted prefix can be continued with exactly the remaining budget. -/
theorem run_after_exhaustion (program : Program) (first second : Nat)
    (source residual : Configuration)
    (paused : run program first source = .exhausted residual) :
    run program second residual = run program (first + second) source := by
  simpa only [paused, resume] using resume_run program first second source

/-- Several resumptions associate, retaining the same whole configuration. -/
theorem resume_assoc (program : Program) (first second : Nat) (outcome : Outcome) :
    resume program second (resume program first outcome) =
      resume program (first + second) outcome := by
  cases outcome <;> simp only [resume]
  exact resume_run program first second _

/-- A residual reached by the executable runner has a genuine path in the
independently authored transition relation. Exhaustion adds no transition. -/
theorem exhausted_has_path (program : Program) (fuel : Nat)
    (source residual : Configuration)
    (paused : run program fuel source = .exhausted residual) :
    (theory program).MultiStep source residual := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk state control frames input output =>
          cases control <;> cases frames <;> simp only [run] at paused
          all_goals try contradiction
          all_goals cases paused; exact .refl _
  | succ fuel ih =>
      cases source with
      | mk state control frames input output =>
          cases control <;> cases frames <;> simp only [run] at paused
          all_goals try contradiction
          all_goals split at paused
          all_goals
            first
            | exact .step (step_transition ‹step program _ = some _›) (ih _ paused)
            | cases paused; exact .refl _

/-- A pause certificate retains the program, starting configuration and paid
transition budget in its indices. It is created by running the existing
machine, rather than by supplying a claimed evaluation result. -/
structure PausedExecution (program : Program) (source : Configuration) (fuel : Nat) where
  residual : Configuration
  exhausted : run program fuel source = .exhausted residual

/-- Return an indexed residual precisely when the executable runner pauses. -/
def pause? (program : Program) (fuel : Nat) (source : Configuration) :
    Option (PausedExecution program source fuel) :=
  match observed : run program fuel source with
  | .exhausted residual => some ⟨residual, observed⟩
  | _ => none

namespace PausedExecution

/-- The certificate exposes an actual path of independently specified steps. -/
theorem path {program : Program} {source : Configuration} {fuel : Nat}
    (paused : PausedExecution program source fuel) :
    (theory program).MultiStep source paused.residual :=
  exhausted_has_path program fuel source paused.residual paused.exhausted

/-- Continue the retained configuration with the same indexed program. -/
def continueWith {program : Program} {source : Configuration} {fuel : Nat}
    (paused : PausedExecution program source fuel) (additional : Nat) : Outcome :=
  run program additional paused.residual

/-- Resumption of a constructed certificate agrees with uninterrupted
execution, including store, alternatives, input, output and terminal faults. -/
theorem continueWith_eq_run {program : Program} {source : Configuration} {fuel : Nat}
    (paused : PausedExecution program source fuel) (additional : Nat) :
    paused.continueWith additional = run program (fuel + additional) source :=
  run_after_exhaustion program fuel additional source paused.residual paused.exhausted

end PausedExecution

/-- The pause factory returns no certificate for either terminal outcome. -/
theorem pause_none_iff (program : Program) (fuel : Nat) (source : Configuration) :
    pause? program fuel source = none ↔
      ∀ residual, run program fuel source ≠ .exhausted residual := by
  unfold pause?
  split
  · rename_i residual observed
    constructor
    · intro impossible
      cases impossible
    · intro never
      exact False.elim (never residual observed)
  · rename_i never
    simpa only [true_iff] using never

end Mettapedia.Languages.MeTTa.PeTTa.Eval
