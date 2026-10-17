import Mettapedia.Computability.StackMachineComposition

/-!
# Supplied traces of the ORIGINAL stack machine

The verifier below checks every supplied successor against `machine.step`, and
checks the exact canonical halting configuration, including scratch stacks.
It does not replace machine execution by a mathematical reference function.
Accepted traces carry a counted original execution; every successful original
execution has a trace of precisely its recorded length.

This is NOT yet serialization or a HOL/MM0 host compiler. Configuration equality
is explicit. An executable uniform descriptor also needs effective transition
tables and finite representations for ALL internal alphabets: Mathlib's FinTM2
record by itself supplies finiteness only for the input alphabet. No polynomial
bound, machine-code extraction or uniform descriptor generation is asserted.
-/

set_option autoImplicit false
namespace Mettapedia.Computability.OriginalMachineTrace
open Turing StateTransition
open Mettapedia.Computability.StackMachineComposition (oneStep outputs_unique)

variable (machine : FinTM2) [DecidableEq machine.Cfg]

/-- Each entry is the next complete configuration, NOT a claimed acceptance bit.
The initial configuration is supplied independently by the input decoder. -/
def replay : machine.Cfg → List machine.Cfg → Option machine.Cfg
  | start, [] => some start
  | start, next :: rest =>
      if machine.step start = some next then replay next rest else none

/-- The accepted physical edges construct an original counted execution. -/
def replayExecution : ∀ (trace : List machine.Cfg) (start finish : machine.Cfg),
    replay machine start trace = some finish →
      EvalsToInTime machine.step start (some finish) trace.length
  | [], start, finish, accepted => by
      have same : start = finish := Option.some.inj accepted
      subst finish
      exact EvalsToInTime.refl machine.step start
  | next :: rest, start, finish, accepted => by
      by_cases edge : machine.step start = some next
      · have remaining : replay machine next rest = some finish := by
          simpa only [replay, if_pos edge] using accepted
        exact EvalsToInTime.trans machine.step 1 rest.length start next
          (some finish) (oneStep edge)
          (replayExecution rest next finish remaining)
      · simp only [replay, if_neg edge] at accepted
        cases accepted

/-- Replay composes at the actual intermediate configuration. -/
theorem replay_append (start : machine.Cfg) (first second : List machine.Cfg) :
    replay machine start (first ++ second) =
      (replay machine start first).bind (fun middle => replay machine middle second) := by
  induction first generalizing start with
  | nil => rfl
  | cons next rest ih =>
      by_cases edge : machine.step start = some next
      · simpa only [List.cons_append, replay, if_pos edge] using ih next
      · simp only [List.cons_append, replay, if_neg edge, Option.bind_none]

/-- A missing, changed or reordered successor is refused at that edge. -/
theorem wrong_successor (start next : machine.Cfg) (rest : List machine.Cfg)
    (wrong : machine.step start ≠ some next) :
    replay machine start (next :: rest) = none := by
  simp only [replay, if_neg wrong]

/-- Construct a trace from an actual successful finite iteration. This is
existential in Prop; it makes no claim to a cheap reverse proof extractor. -/
theorem trace_of_iteration : ∀ (count : Nat) (start finish : machine.Cfg),
    (fun state : Option machine.Cfg => state.bind machine.step)^[count]
      (some start) = some finish →
    ∃ trace, trace.length = count ∧ replay machine start trace = some finish := by
  intro count
  induction count with
  | zero =>
      intro start finish ran
      have same : start = finish := Option.some.inj ran
      subst finish
      exact ⟨[], rfl, rfl⟩
  | succ count ih =>
      intro start finish ran
      rw [Function.iterate_succ_apply] at ran
      cases edge : machine.step start with
      | none =>
          simp only [Option.bind_some, edge] at ran
          have stopped :
              (fun state : Option machine.Cfg => state.bind machine.step)^[count]
                none = none := Function.iterate_fixed (by rfl) count
          rw [stopped] at ran
          cases ran
      | some next =>
          simp only [Option.bind_some, edge] at ran
          obtain ⟨trace, length, accepted⟩ := ih next finish ran
          exact ⟨next :: trace, by simp only [List.length_cons, length],
            by simp only [replay, if_pos edge, accepted]⟩

/-- The endpoint includes the original stack cleanup convention. -/
def accepts (input : List (machine.Γ machine.k₀))
    (output : List (machine.Γ machine.k₁)) (trace : List machine.Cfg) : Bool :=
  decide (replay machine (initList machine input) trace = some (haltList machine output))

def acceptedExecution (input : List (machine.Γ machine.k₀))
    (output : List (machine.Γ machine.k₁)) (trace : List machine.Cfg)
    (accepted : accepts machine input output trace = true) :
    TM2OutputsInTime machine input (some output) trace.length :=
  replayExecution machine trace (initList machine input) (haltList machine output)
    (of_decide_eq_true accepted)

/-- Neither witness search nor a termination premise is needed to check one
supplied finite run. Conversely, a successful run supplies a finite witness. -/
theorem accepts_iff_original_execution
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁)) :
    (∃ trace, accepts machine input output trace = true) ↔
      Nonempty (TM2Outputs machine input (some output)) := by
  constructor
  · rintro ⟨trace, accepted⟩
    exact ⟨(acceptedExecution machine input output trace accepted).toEvalsTo⟩
  · rintro ⟨execution⟩
    obtain ⟨trace, _, accepted⟩ := trace_of_iteration machine execution.steps
      (initList machine input) (haltList machine output) execution.evals_in_steps
    exact ⟨trace, by simp only [accepts, accepted, decide_true]⟩

/-- Two accepted witnesses for one original input cannot disagree on its
canonical output; they need not have the same serialized witness size. -/
theorem accepted_output_unique (input : List (machine.Γ machine.k₀))
    (first second : List (machine.Γ machine.k₁)) (left right : List machine.Cfg)
    (firstAccepted : accepts machine input first left = true)
    (secondAccepted : accepts machine input second right = true) : first = second :=
  outputs_unique (acceptedExecution machine input first left firstAccepted).toEvalsTo
    (acceptedExecution machine input second right secondAccepted).toEvalsTo

end Mettapedia.Computability.OriginalMachineTrace
