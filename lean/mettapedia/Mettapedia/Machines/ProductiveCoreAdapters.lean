import Mettapedia.Machines.MachineRefinement
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Deterministic control cores in the common finite-run interface

A bare core supplies no completed-answer observer. Its missing transition
therefore remains stuck. An answer core supplies a checked final observer;
only that observer constructs a finished outcome. Computational occurrences
retain their ordered source and destination states. They are operational
observations, not external effects or hardware instructions.

Connected traces use the original core transition relation. General laws
relate those traces and reachability to the existing productive-block runner,
exact residuals and cost accounts. The adapters do not classify arbitrary
control computation as silent administration or assume termination.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProductiveCoreAdapters

open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Term Answer : Type}

abbrev Occurrence (State : Type) := State × State

inductive Trace (core : MachineCore Term) : core.State → List (Occurrence core.State) → core.State → Prop where
  | empty (state : core.State) : Trace core state [] state
  | cons {state next final : core.State} {events : List (Occurrence core.State)}
      (step : core.StepRel state next) (following : Trace core next events final) :
      Trace core state ((state, next) :: events) final

theorem Trace.reachable (core : MachineCore Term) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core state events final) : core.Steps state final := by
  induction trace with
  | empty => exact .refl
  | cons step _ ih => exact .head step ih

theorem trace_of_reachable (core : MachineCore Term) {state final : core.State}
    (reachable : core.Steps state final) : ∃ events, Trace core state events final := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .empty _⟩
  | head step _ ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨_, .cons step trace⟩

/-- Iterating the partial core transition retains exactly the connected occurrences. -/
theorem Trace.iteration (core : MachineCore Term) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core state events final) :
    (fun current : Option core.State => current.bind core.step)^[events.length]
      (some state) = some final := by
  induction trace with
  | empty => rfl
  | @cons state next final events step _ ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, Option.bind_some]
      rw [step]
      exact ih

/-- A successful partial iteration constructs a trace of the same length; it cannot
    have passed through a missing transition. -/
theorem trace_of_iteration (core : MachineCore Term) (count : Nat)
    {state final : core.State}
    (ran : (fun current : Option core.State => current.bind core.step)^[count]
      (some state) = some final) :
    ∃ events, Trace core state events final ∧ events.length = count := by
  induction count generalizing state with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at ran
      subst final
      exact ⟨[], .empty _, rfl⟩
  | succ count ih =>
      rw [Function.iterate_succ_apply] at ran
      simp only [Option.bind_some] at ran
      cases step : core.step state with
      | none =>
          rw [step, Function.iterate_fixed (by rfl)] at ran
          cases ran
      | some next =>
          rw [step] at ran
          obtain ⟨events, trace, length⟩ := ih ran
          exact ⟨(state, next) :: events, .cons step trace, by simp [length]⟩

theorem iteration_iff_trace (core : MachineCore Term) (count : Nat)
    (state final : core.State) :
    (fun current : Option core.State => current.bind core.step)^[count]
        (some state) = some final ↔
      ∃ events, Trace core state events final ∧ events.length = count := by
  constructor
  · exact trace_of_iteration core count
  · rintro ⟨events, trace, rfl⟩
    exact trace.iteration core

theorem Trace.append (core : MachineCore Term) {state middle final : core.State}
    {first second : List (Occurrence core.State)} (one : Trace core state first middle)
    (two : Trace core middle second final) : Trace core state (first ++ second) final := by
  induction one with
  | empty => exact two
  | cons step _ ih => exact .cons step (ih two)

def coreMachine (core : MachineCore Term) : Machine core.State (Occurrence core.State) Empty Empty where
  step state := (core.step state).map fun next => .publish [(state, next)] next

theorem core_step (core : MachineCore Term) {state next : core.State}
    (step : core.StepRel state next) :
    (coreMachine core).step state = some (.publish [(state, next)] next) := by
  simp only [coreMachine, MachineCore.StepRel] at step ⊢
  simp only [step, Option.map_some]

theorem core_missing_step (core : MachineCore Term) {state : core.State} (final : core.Final state) :
    (coreMachine core).step state = none := by
  simp only [coreMachine, MachineCore.Final] at final ⊢
  simp only [final, Option.map_none]

theorem core_no_administration (core : MachineCore Term) (state next : core.State) :
    (coreMachine core).step state ≠ some (.silent next) := by
  cases step : core.step state <;> simp [coreMachine, step]

theorem trace_core_run (core : MachineCore Term) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core state events final) :
    (coreMachine core).run events.length state = (events, .exhausted final) := by
  induction trace with
  | empty => rfl
  | cons step _ ih =>
      simp only [List.length_cons, Machine.run, core_step core step, ih, List.singleton_append]

theorem core_run_sound (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    (∃ final, Trace core state ((coreMachine core).run fuel state).1 final ∧
      ((coreMachine core).run fuel state).2 = .exhausted final) ∨
    ∃ final, Trace core state ((coreMachine core).run fuel state).1 final ∧
      ((coreMachine core).run fuel state).2 = .stuck final ∧ core.Final final := by
  induction fuel generalizing state with
  | zero => exact .inl ⟨state, .empty _, rfl⟩
  | succ fuel ih =>
      cases step : core.step state with
      | none =>
          exact .inr ⟨state, by simp only [Machine.run, coreMachine, step, Option.map_none]; exact .empty _,
            by simp only [Machine.run, coreMachine, step, Option.map_none], step⟩
      | some next =>
          have stepped : core.StepRel state next := step
          have advanced := core_step core stepped
          rcases ih next with ⟨final, trace, ending⟩ | ⟨final, trace, ending, stopped⟩
          · exact .inl ⟨final, by simpa only [Machine.run, advanced, List.singleton_append] using Trace.cons stepped trace,
              by simpa only [Machine.run, advanced] using ending⟩
          · exact .inr ⟨final, by simpa only [Machine.run, advanced, List.singleton_append] using Trace.cons stepped trace,
              by simpa only [Machine.run, advanced] using ending, stopped⟩

theorem core_reachable_iff_exhausted (core : MachineCore Term) (state final : core.State) :
    core.Steps state final ↔ ∃ fuel events, (coreMachine core).run fuel state = (events, .exhausted final) := by
  constructor
  · intro reachable
    obtain ⟨events, trace⟩ := trace_of_reachable core reachable
    exact ⟨events.length, events, trace_core_run core trace⟩
  · rintro ⟨fuel, events, ran⟩
    rcases core_run_sound core fuel state with ⟨last, trace, ending⟩ | ⟨last, _, ending, _⟩
    · rw [ran] at trace ending
      cases ending
      exact trace.reachable core
    · rw [ran] at ending
      cases ending

def charge {State : Type} (price : State → Nat) (events : List (Occurrence State)) : Nat :=
  events.foldr (fun event total => price event.1 + total) 0

theorem charge_append {State : Type} (price : State → Nat) (first second : List (Occurrence State)) :
    charge price (first ++ second) = charge price first + charge price second := by
  induction first with
  | nil => simp [charge]
  | cons event rest ih => simpa only [charge, List.foldr_cons, List.cons_append, Nat.add_assoc] using congrArg (price event.1 + ·) ih

theorem charge_unit {State : Type} (events : List (Occurrence State)) :
    charge (fun _ => 1) events = events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [charge, List.foldr_cons, List.length_cons] at ih ⊢; omega

theorem core_spent_is_charge (core : MachineCore Term) (price : core.State → Nat) (fuel : Nat) (state : core.State) :
    (coreMachine core).spent price fuel state = charge price ((coreMachine core).run fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases step : core.step state with
      | none => simp [Machine.spent, Machine.run, coreMachine, step, charge]
      | some next =>
          have advanced := core_step core (show core.StepRel state next from step)
          simp only [Machine.spent, Machine.run, advanced, List.singleton_append, charge, List.foldr_cons]
          exact congrArg (price state + ·) (ih next)

theorem unit_account_le_budget {State Event Verdict Request : Type}
    (machine : Machine State Event Verdict Request) (fuel : Nat) (state : State) :
    machine.spent (fun _ => 1) fuel state ≤ fuel := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      cases step : machine.step state with
      | none => simp [Machine.spent, step]
      | some transition =>
          cases transition with
          | silent next => simp only [Machine.spent, step]; have later := ih next; omega
          | publish events next => simp only [Machine.spent, step]; have later := ih next; omega
          | finish verdict => simp [Machine.spent, step]
          | fail events => simp [Machine.spent, step]
          | call request saved => simp [Machine.spent, step]

theorem core_occurrences_le_budget (core : MachineCore Term) (fuel : Nat) (state : core.State) :
    ((coreMachine core).run fuel state).1.length ≤ fuel := by
  have bounded := unit_account_le_budget (coreMachine core) fuel state
  rw [core_spent_is_charge, charge_unit] at bounded
  exact bounded

def answerMachine (core : AnswerMachineCore Term Answer) : Machine core.State (Occurrence core.State) Answer Empty where
  step state := match core.answer state with
    | some answer => some (.finish answer)
    | none => (core.step state).map fun next => .publish [(state, next)] next

theorem answer_absent_of_step (core : AnswerMachineCore Term Answer) {state next : core.State}
    (step : core.toMachineCore.StepRel state next) : core.answer state = none := by
  cases answer : core.answer state with
  | none => rfl
  | some value =>
      have final := core.answer_final state value answer
      rw [MachineCore.StepRel, final] at step
      cases step

theorem answer_step (core : AnswerMachineCore Term Answer) {state next : core.State}
    (step : core.toMachineCore.StepRel state next) :
    (answerMachine core).step state = some (.publish [(state, next)] next) := by
  simp only [answerMachine, answer_absent_of_step core step]
  simp only [MachineCore.StepRel] at step
  simp only [step, Option.map_some]

theorem observed_finish (core : AnswerMachineCore Term Answer) {state : core.State} {answer : Answer}
    (observed : core.answer state = some answer) :
    (answerMachine core).step state = some (.finish answer) := by
  simp only [answerMachine, observed]

theorem unobserved_stuck (core : AnswerMachineCore Term Answer) {state : core.State}
    (unobserved : core.answer state = none) (stopped : core.toMachineCore.Final state) :
    (answerMachine core).step state = none := by
  simp only [answerMachine, unobserved, MachineCore.Final] at stopped ⊢
  simp only [stopped, Option.map_none]

theorem answer_no_administration (core : AnswerMachineCore Term Answer) (state next : core.State) :
    (answerMachine core).step state ≠ some (.silent next) := by
  cases answer : core.answer state <;> cases step : core.step state <;> simp [answerMachine, answer, step]

theorem trace_answer_run (core : AnswerMachineCore Term Answer) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core.toMachineCore state events final) :
    (answerMachine core).run events.length state = (events, .exhausted final) := by
  induction trace with
  | empty => rfl
  | cons step _ ih =>
      simp only [List.length_cons, Machine.run, answer_step core step, ih, List.singleton_append]

theorem trace_answer_finish (core : AnswerMachineCore Term Answer) {state final : core.State}
    {events : List (Occurrence core.State)} {answer : Answer}
    (trace : Trace core.toMachineCore state events final) (observed : core.answer final = some answer) :
    (answerMachine core).run (events.length + 1) state = (events, .finished answer) := by
  rw [Machine.run_add, trace_answer_run core trace]
  simp only [Machine.continueRun, Machine.run, observed_finish core observed, List.append_nil]

theorem answer_run_sound (core : AnswerMachineCore Term Answer) (fuel : Nat) (state : core.State) :
    ∃ final, Trace core.toMachineCore state ((answerMachine core).run fuel state).1 final ∧
      (((answerMachine core).run fuel state).2 = .exhausted final ∨
        (((answerMachine core).run fuel state).2 = .stuck final ∧ core.answer final = none ∧ core.toMachineCore.Final final) ∨
        ∃ answer, ((answerMachine core).run fuel state).2 = .finished answer ∧ core.answer final = some answer) := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .empty _, .inl rfl⟩
  | succ fuel ih =>
      cases observed : core.answer state with
      | some answer =>
          have finished := observed_finish core observed
          exact ⟨state, by simp only [Machine.run, finished]; exact .empty _,
            .inr (.inr ⟨answer, by simp only [Machine.run, finished], observed⟩)⟩
      | none =>
          cases step : core.step state with
          | none =>
              have stopped := unobserved_stuck core observed step
              exact ⟨state, by simp only [Machine.run, stopped]; exact .empty _,
                .inr (.inl ⟨by simp only [Machine.run, stopped], observed, step⟩)⟩
          | some next =>
              have stepped : core.toMachineCore.StepRel state next := step
              have advanced := answer_step core stepped
              obtain ⟨final, trace, ending⟩ := ih next
              exact ⟨final, by simpa only [Machine.run, advanced, List.singleton_append] using Trace.cons stepped trace,
                by simpa only [Machine.run, advanced] using ending⟩

theorem answer_reachable_iff_finished (core : AnswerMachineCore Term Answer) (state : core.State) (answer : Answer) :
    (∃ final, core.toMachineCore.Steps state final ∧ core.answer final = some answer) ↔
      ∃ fuel events, (answerMachine core).run fuel state = (events, .finished answer) := by
  constructor
  · rintro ⟨final, reachable, observed⟩
    obtain ⟨events, trace⟩ := trace_of_reachable core.toMachineCore reachable
    exact ⟨events.length + 1, events, trace_answer_finish core trace observed⟩
  · rintro ⟨fuel, events, ran⟩
    obtain ⟨final, trace, ending⟩ := answer_run_sound core fuel state
    rw [ran] at trace ending
    rcases ending with impossible | ⟨impossible, _, _⟩ | ⟨value, equal, observed⟩
    · cases impossible
    · cases impossible
    · cases equal
      exact ⟨final, trace.reachable _, observed⟩

theorem produces_iff_finished (core : AnswerMachineCore Term Answer) (term : Term) (answer : Answer) :
    core.Produces term answer ↔ ∃ fuel events, (answerMachine core).run fuel (core.load term) = (events, .finished answer) :=
  answer_reachable_iff_finished core (core.load term) answer

theorem trace_core_resume (core : MachineCore Term) {state residual : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core state events residual) (second : Nat) :
    (coreMachine core).run (events.length + second) state =
      (events ++ ((coreMachine core).run second residual).1, ((coreMachine core).run second residual).2) :=
  (coreMachine core).established_and_pending events.length second state residual events (trace_core_run core trace)

theorem trace_answer_resume (core : AnswerMachineCore Term Answer) {state residual : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core.toMachineCore state events residual) (second : Nat) :
    (answerMachine core).run (events.length + second) state =
      (events ++ ((answerMachine core).run second residual).1, ((answerMachine core).run second residual).2) :=
  (answerMachine core).established_and_pending events.length second state residual events (trace_answer_run core trace)

theorem core_answer_occurrences_agree (core : AnswerMachineCore Term Answer) (fuel : Nat) (state : core.State) :
    ((coreMachine core.toMachineCore).run fuel state).1 = ((answerMachine core).run fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : core.answer state with
      | some answer =>
          have stopped := core_missing_step core.toMachineCore (core.answer_final state answer observed)
          simp only [Machine.run, stopped, observed_finish core observed]
      | none =>
          cases step : core.step state with
          | none =>
              simp only [Machine.run, core_missing_step core.toMachineCore step, unobserved_stuck core observed step]
          | some next =>
              have stepped : core.toMachineCore.StepRel state next := step
              simp only [Machine.run, core_step core.toMachineCore stepped, answer_step core stepped]
              exact congrArg ([(state, next)] ++ ·) (ih next)

def computationalPrice (core : MachineCore Term) (price : core.State → Nat) (state : core.State) : Nat :=
  if (core.step state).isSome then price state else 0

theorem answer_spent_is_charge (core : AnswerMachineCore Term Answer) (price : core.State → Nat)
    (fuel : Nat) (state : core.State) :
    (answerMachine core).spent (computationalPrice core.toMachineCore price) fuel state =
      charge price ((answerMachine core).run fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : core.answer state with
      | some answer =>
          simp [Machine.spent, Machine.run, observed_finish core observed, computationalPrice,
            core.answer_final state answer observed, charge]
      | none =>
          cases step : core.step state with
          | none => simp [Machine.spent, Machine.run, unobserved_stuck core observed step, charge]
          | some next =>
              have advanced := answer_step core (show core.toMachineCore.StepRel state next from step)
              simp only [Machine.spent, Machine.run, advanced, computationalPrice, step, Option.isSome_some,
                if_true, List.singleton_append, charge, List.foldr_cons]
              exact congrArg (price state + ·) (ih next)

theorem answer_computational_count (core : AnswerMachineCore Term Answer) (fuel : Nat) (state : core.State) :
    (answerMachine core).spent (computationalPrice core.toMachineCore (fun _ => 1)) fuel state =
      ((answerMachine core).run fuel state).1.length := by
  rw [answer_spent_is_charge, charge_unit]

theorem trace_answer_account_resume (core : AnswerMachineCore Term Answer) {state residual : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core.toMachineCore state events residual)
    (price : core.State → Nat) (second : Nat) :
    (answerMachine core).spent (computationalPrice core.toMachineCore price) (events.length + second) state =
      charge price events + (answerMachine core).spent (computationalPrice core.toMachineCore price) second residual := by
  rw [Machine.spent_add, answer_spent_is_charge, trace_answer_run core trace]
  rfl

theorem answer_instruction_count (core : AnswerMachineCore Term Answer) (fuel : Nat) (state : core.State) :
    (answerMachine core).spent (fun _ => 1) fuel state = ((answerMachine core).run fuel state).1.length +
      (match ((answerMachine core).run fuel state).2 with | .finished _ => 1 | _ => 0) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases observed : core.answer state with
      | some answer => simp [Machine.spent, Machine.run, observed_finish core observed]
      | none =>
          cases step : core.step state with
          | none => simp [Machine.spent, Machine.run, unobserved_stuck core observed step]
          | some next =>
              have advanced := answer_step core (show core.toMachineCore.StepRel state next from step)
              simp only [Machine.spent, Machine.run, advanced, List.singleton_append, List.length_cons]
              rw [ih next]
              omega

theorem answer_occurrences_le_budget (core : AnswerMachineCore Term Answer) (fuel : Nat) (state : core.State) :
    ((answerMachine core).run fuel state).1.length ≤ fuel := by
  have bounded := unit_account_le_budget (answerMachine core) fuel state
  rw [answer_instruction_count] at bounded
  omega

theorem perpetual_computation (core : AnswerMachineCore Term Answer) (region : core.State → Prop)
    (closed : ∀ state, region state → ∃ next, core.toMachineCore.StepRel state next ∧ region next)
    (fuel : Nat) (state : core.State) (inside : region state) :
    ∃ events residual, (answerMachine core).run fuel state = (events, .exhausted residual) ∧
      Trace core.toMachineCore state events residual ∧ events.length = fuel ∧ region residual := by
  induction fuel generalizing state with
  | zero => exact ⟨[], state, rfl, .empty _, rfl, inside⟩
  | succ fuel ih =>
      obtain ⟨next, step, nextInside⟩ := closed state inside
      obtain ⟨events, residual, ran, trace, count, remaining⟩ := ih next nextInside
      exact ⟨(state, next) :: events, residual,
        by simp only [Machine.run, answer_step core step, ran, List.singleton_append],
        .cons step trace, by simp only [List.length_cons, count], remaining⟩

/-- Observing a missing transition takes a boundary poll after the last
computational occurrence. It does not manufacture a completed answer. -/
theorem trace_core_stuck (core : MachineCore Term) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core state events final)
    (stopped : core.Final final) :
    (coreMachine core).run (events.length + 1) state = (events, .stuck final) := by
  rw [Machine.run_add, trace_core_run core trace]
  simp only [Machine.continueRun, Machine.run, core_missing_step core stopped,
    List.append_nil]

theorem core_reachable_iff_stuck (core : MachineCore Term) (state final : core.State) :
    (core.Steps state final ∧ core.Final final) ↔
      ∃ fuel events, (coreMachine core).run fuel state = (events, .stuck final) := by
  constructor
  · rintro ⟨reachable, stopped⟩
    obtain ⟨events, trace⟩ := trace_of_reachable core reachable
    exact ⟨events.length + 1, events, trace_core_stuck core trace stopped⟩
  · rintro ⟨fuel, events, ran⟩
    rcases core_run_sound core fuel state with ⟨last, _, ending⟩ | ⟨last, trace, ending, stopped⟩
    · rw [ran] at ending
      cases ending
    · rw [ran] at trace ending
      cases ending
      exact ⟨trace.reachable core, stopped⟩

theorem trace_answer_stuck (core : AnswerMachineCore Term Answer) {state final : core.State}
    {events : List (Occurrence core.State)} (trace : Trace core.toMachineCore state events final)
    (unobserved : core.answer final = none) (stopped : core.toMachineCore.Final final) :
    (answerMachine core).run (events.length + 1) state = (events, .stuck final) := by
  rw [Machine.run_add, trace_answer_run core trace]
  simp only [Machine.continueRun, Machine.run, unobserved_stuck core unobserved stopped,
    List.append_nil]

/-- A stopped computation is stuck exactly when its actual final observer
has no answer. The same transition endpoint can carry a completed answer in
another observer profile. -/
theorem answer_reachable_iff_stuck (core : AnswerMachineCore Term Answer) (state final : core.State) :
    (core.toMachineCore.Steps state final ∧ core.answer final = none ∧ core.toMachineCore.Final final) ↔
      ∃ fuel events, (answerMachine core).run fuel state = (events, .stuck final) := by
  constructor
  · rintro ⟨reachable, unobserved, stopped⟩
    obtain ⟨events, trace⟩ := trace_of_reachable core.toMachineCore reachable
    exact ⟨events.length + 1, events, trace_answer_stuck core trace unobserved stopped⟩
  · rintro ⟨fuel, events, ran⟩
    obtain ⟨last, trace, ending⟩ := answer_run_sound core fuel state
    rw [ran] at trace ending
    rcases ending with impossible | ⟨same, unobserved, stopped⟩ | ⟨_, impossible, _⟩
    · cases impossible
    · cases same
      exact ⟨trace.reachable _, unobserved, stopped⟩
    · cases impossible

/-- The deterministic adapter diverges precisely when no reachable state
has lost its next computational transition. No termination premise or
administrative classification is imposed on those transitions. -/
theorem core_diverges_iff_no_reachable_final (core : MachineCore Term) (state : core.State) :
    (coreMachine core).DivergesWithin state ↔
      ∀ final, core.Steps state final → ¬ core.Final final := by
  constructor
  · intro diverges final reachable stopped
    obtain ⟨fuel, events, ran⟩ := (core_reachable_iff_stuck core state final).mp ⟨reachable, stopped⟩
    exact diverges.not_stuck (coreMachine core) fuel final (congrArg Prod.snd ran)
  · intro continues fuel
    rcases core_run_sound core fuel state with ⟨last, _, ending⟩ | ⟨last, trace, _, stopped⟩
    · exact ⟨last, ending⟩
    · exact False.elim (continues last (trace.reachable core) stopped)

/-- Adding a sound final-answer observer preserves computational divergence.
It distinguishes the two terminal outcomes without changing any continuing
computation or assuming that all source programs terminate. -/
theorem answer_diverges_iff_core (core : AnswerMachineCore Term Answer) (state : core.State) :
    (answerMachine core).DivergesWithin state ↔
      (coreMachine core.toMachineCore).DivergesWithin state := by
  rw [core_diverges_iff_no_reachable_final]
  constructor
  · intro diverges final reachable stopped
    obtain ⟨events, trace⟩ := trace_of_reachable core.toMachineCore reachable
    cases observed : core.answer final with
    | none =>
        have ran := trace_answer_stuck core trace observed stopped
        exact diverges.not_stuck (answerMachine core) (events.length + 1) final
          (congrArg Prod.snd ran)
    | some answer =>
        have ran := trace_answer_finish core trace observed
        obtain ⟨residual, exhausted⟩ := diverges (events.length + 1)
        rw [ran] at exhausted
        cases exhausted
  · intro continues fuel
    obtain ⟨last, trace, ending⟩ := answer_run_sound core fuel state
    rcases ending with exhausted | ⟨_, _, stopped⟩ | ⟨answer, _, observed⟩
    · exact ⟨last, exhausted⟩
    · exact False.elim (continues last (trace.reachable _) stopped)
    · exact False.elim (continues last (trace.reachable _) (core.answer_final last answer observed))

end Mettapedia.Machines.ProductiveCoreAdapters
