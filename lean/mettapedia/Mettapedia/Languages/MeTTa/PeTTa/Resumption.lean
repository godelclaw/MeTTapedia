import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Machines.ProductiveCoreAdapters

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

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval.CommonMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines
open Mettapedia.Machines.ProductiveCoreAdapters
open SpaceSemantics (Program)
open DeclarativeSpec (Runs)

/-- The existing evaluator supplies the control core unchanged. The question
contains its initial effect store; resumption uses the entire Configuration,
including bindings, ordered pending controls, caller frames and I/O. -/
def core (program : Program) : MachineCore (Effects.State × Atom) where
  State := Configuration
  load question := start question.1 question.2
  step := Eval.step program

/-- Terminal observations preserve the evaluator's distinction between a
completed answer list and a fault with its reached configuration. Exhaustion
is never a terminal observation. -/
def observe (source : Configuration) : Option Outcome :=
  match source.control, source.frames with
  | .returned answers, [] => .some (.complete source.state answers source.input source.output)
  | .fault reason, _ => .some (.fault reason source)
  | _, _ => none

theorem observe_final (program : Program) (source : Configuration) (result : Outcome)
    (observed : observe source = some result) : Eval.step program source = none := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals first | rfl | simp [observe] at observed

/-- The current evaluator has no unclassified missing transition. Malformed
forms handled by its source rules become explicit fault configurations;
ordinary unknown syntax follows those rules' data path. -/
theorem observe_of_missing_step (program : Program) (source : Configuration)
    (missing : Eval.step program source = none) : ∃ result, observe source = some result := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals first
        | exact ⟨_, rfl⟩
        | (simp only [Eval.step] at missing
           repeat' first | contradiction | split at missing)

theorem final_iff_observed (program : Program) (source : Configuration) :
    (core program).Final source ↔ ∃ result, observe source = some result :=
  ⟨observe_of_missing_step program source, fun ⟨result, observed⟩ =>
    observe_final program source result observed⟩

/-- This packages the actual deterministic step, not a successor-list search
policy. Its terminal answer type includes the source fault constructor. -/
def answerCore (program : Program) : AnswerMachineCore (Effects.State × Atom) Outcome where
  toMachineCore := core program
  answer := observe
  answer_final := observe_final program

/-- The existing common adapter records connected computational occurrences.
Its `.finished (.fault reason reached)` observes a terminal source fault; it
is not the common `.faulted` outcome and is not successful evaluation. -/
def machine (program : Program) :
    GSLT.Distinction.ProductiveBlocks.Machine Configuration (Configuration × Configuration) Outcome Empty :=
  answerMachine (answerCore program)

theorem core_step_iff_source (program : Program) (source target : Configuration) :
    (core program).StepRel source target ↔ DeclarativeSpec.Transition program source target :=
  step_iff_transition program source target

theorem observed_has_derivation (program : Program) (source : Configuration) (result : Outcome)
    (observed : observe source = some result) : Runs program source result := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames <;> simp only [observe] at observed
      all_goals first
        | contradiction
        | (cases Option.some.inj observed; exact .completed rfl rfl)
        | (cases Option.some.inj observed; exact .fault rfl)

theorem derivation_reaches_observation {program : Program} {source : Configuration} {result : Outcome}
    (derivation : Runs program source result) :
    ∃ final, (core program).Steps source final ∧ observe final = some result := by
  induction derivation with
  | completed control frames =>
      exact ⟨_, .refl, by simp only [observe, control, frames]⟩
  | fault control =>
      exact ⟨_, .refl, by simp only [observe, control]⟩
  | next transition _ ih =>
      obtain ⟨final, reached, observed⟩ := ih
      exact ⟨final, .head (transition_step transition) reached, observed⟩

theorem reached_observation_has_derivation {program : Program} {source final : Configuration}
    {result : Outcome} (reached : (core program).Steps source final)
    (observed : observe final = some result) : Runs program source result := by
  induction reached using Relation.ReflTransGen.head_induction_on with
  | refl => exact observed_has_derivation program _ result observed
  | head transition _ ih => exact .next (step_transition transition) ih

/-- Independent source derivations are exactly the common adapter's finite
terminal observations, retaining the full store, answer occurrences and I/O,
or the full reached fault configuration. -/
theorem finished_iff_source (program : Program) (source : Configuration) (result : Outcome) :
    (∃ fuel events, (machine program).run fuel source = (events, .finished result)) ↔
      Runs program source result := by
  change (∃ fuel events, (answerMachine (answerCore program)).run fuel source = (events, .finished result)) ↔ _
  rw [← answer_reachable_iff_finished (answerCore program) source result]
  exact ⟨fun ⟨final, reached, observed⟩ => reached_observation_has_derivation reached observed,
    derivation_reaches_observation⟩

theorem loaded_iff_source (program : Program) (state : Effects.State) (expression : Atom) (result : Outcome) :
    (answerCore program).Produces (state, expression) result ↔
      Runs program (start state expression) result :=
  (produces_iff_finished (answerCore program) (state, expression) result).trans
    (finished_iff_source program (start state expression) result)

/-- The finite runner comparison excludes exhaustion, which is retained work
and has no independent completed derivation. -/
theorem finished_iff_eval (program : Program) (source : Configuration) (result : Outcome)
    (terminal : ∀ pending, result ≠ .exhausted pending) :
    (∃ fuel events, (machine program).run fuel source = (events, .finished result)) ↔
      ∃ fuel, Eval.run program fuel source = result := by
  rw [finished_iff_source]
  exact ⟨derivation_has_run, fun ⟨fuel, computed⟩ =>
    run_has_derivation program fuel source result terminal computed⟩

/-- A suspended budget keeps the actual caller and search stack. Continuing
from this residual concatenates occurrences without rerunning earlier effects. -/
theorem resume (program : Program) (source residual : Configuration)
    (first second : Nat) (events : List (Configuration × Configuration))
    (paused : (machine program).run first source = (events, .exhausted residual)) :
    (machine program).run (first + second) source =
      (events ++ ((machine program).run second residual).1,
        ((machine program).run second residual).2) :=
  (machine program).established_and_pending first second source residual events paused

theorem no_stuck (program : Program) (fuel : Nat) (source residual : Configuration) :
    ((machine program).run fuel source).2 ≠ .stuck residual := by
  intro stuck
  obtain ⟨final, _, ending⟩ := answer_run_sound (answerCore program) fuel source
  change ((machine program).run fuel source).2 = .exhausted final ∨
    (((machine program).run fuel source).2 = .stuck final ∧ observe final = none ∧
      Eval.step program final = none) ∨
    (∃ answer, ((machine program).run fuel source).2 = .finished answer ∧
      observe final = some answer) at ending
  rw [stuck] at ending
  rcases ending with impossible | ⟨_, unobserved, missing⟩ | ⟨_, impossible, _⟩
  · cases impossible
  · obtain ⟨result, observed⟩ := observe_of_missing_step program final missing
    rw [unobserved] at observed
    cases observed
  · cases impossible

#print axioms finished_iff_source
#print axioms final_iff_observed
#print axioms resume

namespace Controls

private def program : Program := { equations := [], declarations := [] }

/-- The older alternative is saved in a sequence frame while the first one
runs. It is not scheduled by interpreting a successor list as DFS. -/
theorem first_alternative_keeps_older_work (state : Effects.State)
    (first : Control) (remaining : List Control) (answers input output : List Atom)
    (older : List Frame) :
    (core program).step ⟨state, .sequence (first :: remaining) answers, older, input, output⟩ =
      some ⟨state, first, .sequence remaining answers :: older, input, output⟩ :=
  transition_step (program := program)
    (source := ⟨state, .sequence (first :: remaining) answers, older, input, output⟩)
    (.sequence_enter rfl)

private def printing (value : Atom) : Control :=
  .arguments [] (.function "println!") [] [value] 0

private def beforePrint (state : Effects.State) : Configuration :=
  ⟨state, printing (.symbol "first"), [], [.symbol "pending-input"], [.symbol "earlier"]⟩

private def afterPrint (state : Effects.State) : Configuration :=
  ⟨state, .returned [Effects.boolean true], [], [.symbol "pending-input"],
    [.symbol "earlier", .symbol "first"]⟩

theorem effect_before_pause (state : Effects.State) :
    (machine program).run 1 (beforePrint state) =
      ([(beforePrint state, afterPrint state)], .exhausted (afterPrint state)) := rfl

theorem resume_keeps_effect_once (state : Effects.State) :
    (machine program).run 1 (afterPrint state) =
      ([], .finished (.complete state [Effects.boolean true] [.symbol "pending-input"]
        [.symbol "earlier", .symbol "first"])) := rfl

theorem ordered_alternative_effects (state : Effects.State) :
    ((machine program).run 8
      ⟨state, .sequence [printing (.symbol "first"), printing (.symbol "second")] [],
        [], [.symbol "pending-input"], [.symbol "earlier"]⟩).2 =
      .finished (.complete state [Effects.boolean true, Effects.boolean true]
        [.symbol "pending-input"] [.symbol "earlier", .symbol "first", .symbol "second"]) := rfl

private def committed (state : Effects.State) : Configuration :=
  ⟨state, .returned [.symbol "value"],
    [.select [] [(.var "x", .expression [.symbol "empty"]), (.var "x", .symbol "fallback")]],
    [.symbol "pending-input"], [.symbol "earlier"]⟩

/-- A selected case whose body returns no answers does not reopen the later
matching row. The common adapter preserves the evaluator's commit point. -/
theorem selected_empty_body_stays_empty (state : Effects.State) :
    ((machine program).run 6 (committed state)).2 =
      .finished (.complete state [] [.symbol "pending-input"] [.symbol "earlier"]) := by
  simp [machine, answerMachine, answerCore, core, GSLT.Distinction.ProductiveBlocks.Machine.run,
    observe, Eval.step, committed, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem selected_empty_body_cannot_fall_through (state : Effects.State) :
    ((machine program).run 6 (committed state)).2 ≠
      .finished (.complete state [.symbol "fallback"] [.symbol "pending-input"] [.symbol "earlier"]) := by
  rw [selected_empty_body_stays_empty]
  intro impossible
  cases impossible

theorem fault_keeps_reached_configuration (state : Effects.State) (older : List Frame) :
    let reached : Configuration :=
      ⟨state, .fault (.invalidArguments "parse"), older,
        [.symbol "pending-input"], [.symbol "already-printed"]⟩
    (machine program).run 1 reached =
      ([], .finished (.fault (.invalidArguments "parse") reached)) := rfl

theorem fault_is_not_empty_success (state : Effects.State) :
    observe ⟨state, .fault (.invalidArguments "parse"), [], [], [.symbol "already-printed"]⟩ ≠
      some (.complete state [] [] [.symbol "already-printed"]) := by
  intro impossible
  cases impossible

/-- A malformed case row reaches the independently specified fault, retaining
its store and older continuation. It is not an unexplained stuck state. -/
theorem malformed_case_is_source_fault (state : Effects.State) (older : List Frame)
    (input output : List Atom) :
    let source : Configuration :=
      ⟨state, .evaluate [] (.expression [.symbol "case", .symbol "value",
        .expression [.symbol "malformed-row"]]), older, input, output⟩
    ∃ fuel events, (machine program).run fuel source =
      (events, .finished (.fault (.invalidArguments "case")
        { source with control := .fault (.invalidArguments "case") })) := by
  dsimp only
  apply (finished_iff_source program _ _).mpr
  exact .next (.case_bad rfl rfl) (.fault rfl)

theorem returned_child_is_not_terminal (state : Effects.State) (frame : Frame)
    (older : List Frame) (answers input output : List Atom) :
    observe ⟨state, .returned answers, frame :: older, input, output⟩ = none := rfl

theorem zero_budget_keeps_pending_work (state : Effects.State) :
    (machine program).run 0 (beforePrint state) = ([], .exhausted (beforePrint state)) := rfl

#print axioms effect_before_pause
#print axioms ordered_alternative_effects
#print axioms selected_empty_body_stays_empty
#print axioms selected_empty_body_cannot_fall_through
#print axioms fault_keeps_reached_configuration
#print axioms fault_is_not_empty_success
#print axioms malformed_case_is_source_fault

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Eval.CommonMachine
