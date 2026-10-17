import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Retained execution without accumulating an event journal

This runner executes the original transition function but retains only its
outcome. Its independently recursive implementation does not construct the
accumulated event list. Exact correspondence preserves verdicts, faults,
requests and residual states at every budget, including resumption.

This is appropriate only when the accumulated journal is not a required
observation. Individual transitions may still construct events and perform
substantial work. Erasing the observation does not remove that work, execute
an external request, or authorize dropping observable effects or provenance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OutcomeRunner

open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {State Event Verdict Request : Type}

def run (machine : Machine State Event Verdict Request) :
    Nat → State → Outcome State Verdict Request
  | 0, state => .exhausted state
  | fuel + 1, state =>
      match machine.step state with
      | none => .stuck state
      | some (.silent next) | some (.publish _ next) => run machine fuel next
      | some (.finish verdict) => .finished verdict
      | some (.fail _) => .faulted
      | some (.call request saved) => .suspended request saved

theorem run_eq (machine : Machine State Event Verdict Request) (fuel : Nat) (state : State) :
    run machine fuel state = (machine.run fuel state).2 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp only [run, Machine.run, advanced]
      | some transition =>
          cases transition <;> simp [run, Machine.run, advanced, ih]

def resume (machine : Machine State Event Verdict Request) (fuel : Nat) :
    Outcome State Verdict Request → Outcome State Verdict Request
  | .exhausted state => run machine fuel state
  | outcome => outcome

theorem resume_eq (machine : Machine State Event Verdict Request) (fuel : Nat)
    (observation : List Event × Outcome State Verdict Request) :
    resume machine fuel observation.2 = (machine.continueRun fuel observation).2 := by
  rcases observation with ⟨events, outcome⟩
  cases outcome <;> simp [resume, Machine.continueRun, run_eq]

theorem run_add (machine : Machine State Event Verdict Request) (first later : Nat)
    (state : State) :
    run machine (first + later) state = resume machine later (run machine first state) := by
  rw [run_eq, machine.run_add, ← resume_eq, ← run_eq]

theorem resume_add (machine : Machine State Event Verdict Request) (first later : Nat)
    (outcome : Outcome State Verdict Request) :
    resume machine later (resume machine first outcome) =
      resume machine (first + later) outcome := by
  cases outcome with
  | exhausted state => exact (run_add machine first later state).symm
  | _ => rfl

namespace Controls

private def machine : Machine Nat Nat Nat Nat where
  step state := match state with
    | 0 => some (.publish [7, 7] 1)
    | 1 => some (.finish 42)
    | 2 => some (.call 9 3)
    | 3 => some (.fail [11])
    | _ => none

theorem check_mode_keeps_result : run machine 2 0 = .finished 42 := rfl

theorem recording_keeps_duplicate_events : (machine.run 2 0).1 = [7, 7] := rfl

theorem budget_is_not_completion : run machine 0 0 = .exhausted 0 := rfl

theorem request_keeps_residual : run machine 2 2 = .suspended 9 3 := rfl

theorem resume_does_not_execute_request :
    resume machine 10 (run machine 2 2) = .suspended 9 3 := rfl

theorem refusal_keeps_fault : run machine 2 3 = .faulted := rfl

theorem stuck_is_not_refusal : run machine 2 4 = .stuck 4 := rfl

theorem split_execution_is_exact :
    resume machine 1 (run machine 1 0) = run machine 2 0 := rfl

end Controls
end Mettapedia.Machines.OutcomeRunner
