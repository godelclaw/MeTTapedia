import Mettapedia.Machines.MachineRefinement
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Distinction.SpanTransport
import Mettapedia.Machines.Cursor.Protocol

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

/-! ## Total strategy ticks and actual core traces -/

/-- A fixed missing-transition strategy retains its state. This operation is
for reproducible iteration; it does not turn a stuck state into a verdict. -/
def retainedTick (core : MachineCore Term) (state : core.State) : core.State :=
  (core.step state).getD state

theorem retainedTick_trace (core : MachineCore Term) (budget : Nat) (state : core.State) :
    ∃ events, Trace core state events ((retainedTick core)^[budget] state) ∧ events.length ≤ budget := by
  induction budget generalizing state with
  | zero => exact ⟨[], .empty _, Nat.zero_le _⟩
  | succ budget ih =>
      cases stepped : core.step state with
      | none =>
          have fixed : retainedTick core state = state := by simp [retainedTick, stepped]
          rw [Function.iterate_fixed fixed]
          exact ⟨[], .empty _, Nat.zero_le _⟩
      | some next =>
          obtain ⟨events, trace, count⟩ := ih next
          have moved : retainedTick core state = next := by simp [retainedTick, stepped]
          rw [Function.iterate_succ_apply, moved]
          exact ⟨(state, next) :: events, .cons stepped trace, by simpa using Nat.succ_le_succ count⟩

/-- A strategy ending at a checked answer has an actual terminating machine
run with at most one finishing transition beyond its supplied tick budget. -/
theorem retainedTick_finished (core : AnswerMachineCore Term Answer) (budget : Nat)
    (state : core.State) (answer : Answer)
    (observed : core.answer ((retainedTick core.toMachineCore)^[budget] state) = some answer) :
    ∃ fuel events, fuel ≤ budget + 1 ∧
      (answerMachine core).run fuel state = (events, .finished answer) := by
  obtain ⟨events, trace, count⟩ := retainedTick_trace core.toMachineCore budget state
  exact ⟨events.length + 1, events, Nat.add_le_add_right count 1,
    trace_answer_finish core trace observed⟩

/-! ## Partial folds with a retained refused suffix -/

namespace RetainedFold

variable {Item Accumulator : Type}

/-- Raw execution state. A table supplied by a caller is not authenticated
evidence. Sound publication uses the proved run from its intended initial
state, or a separately validated prefix under the same fixed consumer. -/
structure Work (Item Accumulator : Type) where
  pending : List Item
  accumulator : Accumulator
  inspected : Nat
  refused : Bool

def start (items : List Item) (accumulator : Accumulator) : Work Item Accumulator :=
  ⟨items, accumulator, 0, false⟩

def Work.settled (work : Work Item Accumulator) : Bool := work.refused || work.pending.isEmpty

def reference (consume : Accumulator → Item → Option Accumulator) :
    Accumulator → List Item → Option Accumulator
  | accumulator, [] => some accumulator
  | accumulator, item :: rest => (consume accumulator item).bind (fun next => reference consume next rest)

def Work.meaning (consume : Accumulator → Item → Option Accumulator)
    (work : Work Item Accumulator) : Option Accumulator :=
  if work.refused then none else reference consume work.accumulator work.pending

/-- One original row is consumed. On refusal the old accumulator, refused
head and complete later suffix are retained. -/
def tick (consume : Accumulator → Item → Option Accumulator)
    (work : Work Item Accumulator) : Work Item Accumulator :=
  if work.refused then work else
    match work.pending with
    | [] => work
    | item :: rest =>
        match consume work.accumulator item with
        | none => { work with inspected := work.inspected + 1, refused := true }
        | some next => ⟨rest, next, work.inspected + 1, false⟩

theorem tick_meaning (consume : Accumulator → Item → Option Accumulator)
    (work : Work Item Accumulator) : (tick consume work).meaning consume = work.meaning consume := by
  rcases work with ⟨pending, accumulator, inspected, refused⟩
  cases refused with
  | true => rfl
  | false =>
      cases pending with
      | nil => rfl
      | cons item rest =>
          cases result : consume accumulator item <;> simp [tick, Work.meaning, reference, result]

theorem tick_settled (consume : Accumulator → Item → Option Accumulator)
    (work : Work Item Accumulator) (settled : work.settled = true) : tick consume work = work := by
  rcases work with ⟨pending, accumulator, inspected, refused⟩
  cases refused with
  | true => rfl
  | false =>
      cases pending with
      | nil => rfl
      | cons item rest => simp [Work.settled] at settled

def advance (consume : Accumulator → Item → Option Accumulator) (budget : Nat)
    (work : Work Item Accumulator) : Work Item Accumulator := (tick consume)^[budget] work

theorem advance_add (consume : Accumulator → Item → Option Accumulator) (first second : Nat)
    (work : Work Item Accumulator) :
    advance consume (first + second) work = advance consume second (advance consume first work) := by
  change (tick consume)^[first + second] work = (tick consume)^[second] ((tick consume)^[first] work)
  rw [Nat.add_comm first second, Function.iterate_add_apply]

theorem refused_suffix (consume : Accumulator → Item → Option Accumulator)
    (accumulator : Accumulator) (item : Item) (rest : List Item) (inspected : Nat)
    (refused : consume accumulator item = none) :
    tick consume ⟨item :: rest, accumulator, inspected, false⟩ =
      ⟨item :: rest, accumulator, inspected + 1, true⟩ := by simp [tick, refused]

theorem advance_meaning (consume : Accumulator → Item → Option Accumulator) (budget : Nat)
    (work : Work Item Accumulator) : (advance consume budget work).meaning consume = work.meaning consume := by
  induction budget generalizing work with
  | zero => rfl
  | succ budget ih =>
      exact (ih (tick consume work)).trans (tick_meaning consume work)

theorem settled_within (consume : Accumulator → Item → Option Accumulator) (budget : Nat)
    (work : Work Item Accumulator) (enough : work.pending.length ≤ budget) :
    (advance consume budget work).settled = true := by
  induction budget generalizing work with
  | zero =>
      have empty : work.pending = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero enough)
      simp [advance, Work.settled, empty]
  | succ budget ih =>
      cases settled : work.settled with
      | true =>
          rw [advance, Function.iterate_fixed (tick_settled consume work settled)]
          exact settled
      | false =>
          rcases work with ⟨pending, accumulator, inspected, refused⟩
          cases refused with
          | true => simp [Work.settled] at settled
          | false =>
              cases pending with
              | nil => simp [Work.settled] at settled
              | cons item rest =>
                  change (advance consume budget (tick consume _)).settled = true
                  cases result : consume accumulator item with
                  | none =>
                      have done : (tick consume ⟨item :: rest, accumulator, inspected, false⟩).settled = true := by
                        simp [tick, result, Work.settled]
                      rw [advance, Function.iterate_fixed (tick_settled consume _ done)]
                      exact done
                  | some next =>
                      simp only [tick, Bool.false_eq_true, ↓reduceIte, result]
                      exact ih ⟨rest, next, inspected + 1, false⟩ (by simpa using enough)

/-- Only completed unrejected work exposes its accumulator. Authenticity of
the starting accumulator remains a separate invariant. -/
def Work.result (work : Work Item Accumulator) : Option Accumulator :=
  if work.refused then none else if work.pending.isEmpty then some work.accumulator else none

theorem result_meaning (consume : Accumulator → Item → Option Accumulator)
    (work : Work Item Accumulator) (settled : work.settled = true) :
    work.result = work.meaning consume := by
  rcases work with ⟨pending, accumulator, inspected, refused⟩
  cases refused with
  | true => rfl
  | false =>
      have empty : pending = [] := by simpa [Work.settled] using settled
      simp [empty, Work.result, Work.meaning, reference]

theorem complete_exact (consume : Accumulator → Item → Option Accumulator)
    (items : List Item) (accumulator : Accumulator) :
    (advance consume items.length (start items accumulator)).result = reference consume accumulator items := by
  rw [result_meaning consume _ (settled_within consume _ _ (by rfl)), advance_meaning]
  rfl

def core (consume : Accumulator → Item → Option Accumulator) :
    AnswerMachineCore (List Item × Accumulator) (Work Item Accumulator) where
  State := Work Item Accumulator
  load input := start input.1 input.2
  step work := if work.settled then none else some (tick consume work)
  answer work := if work.settled then some work else none
  answer_final := by intro work result; split <;> simp_all

theorem retainedTick_eq (consume : Accumulator → Item → Option Accumulator) :
    retainedTick (core consume).toMachineCore = tick consume := by
  funext work
  cases settled : work.settled with
  | false => simp [retainedTick, core, settled]; rfl
  | true => simp [retainedTick, core, settled, tick_settled consume work settled]; rfl

theorem machine_completes (consume : Accumulator → Item → Option Accumulator)
    (items : List Item) (accumulator : Accumulator) :
    ∃ fuel events report, fuel ≤ items.length + 1 ∧
      (answerMachine (core consume)).run fuel (start items accumulator) = (events, .finished report) ∧
      report.result = reference consume accumulator items := by
  let final := advance consume items.length (start items accumulator)
  have observed : (core consume).answer final = some final := by
    simp only [core]
    exact if_pos (settled_within consume _ _ (by rfl))
  have finalTick : (retainedTick (core consume).toMachineCore)^[items.length] (start items accumulator) = final := by
    rw [retainedTick_eq]
    rfl
  obtain ⟨fuel, events, bounded, finished⟩ :=
    retainedTick_finished (core consume) items.length (start items accumulator) final (by simpa [finalTick] using observed)
  exact ⟨fuel, events, final, bounded, finished, complete_exact consume items accumulator⟩

/-- Every actual finished run from the intended load has the original fold
result. The report cannot be replaced by an arbitrary raw accumulator. -/
theorem finished_result (consume : Accumulator → Item → Option Accumulator)
    (items : List Item) (accumulator : Accumulator) {fuel : Nat}
    {events : List (Occurrence (Work Item Accumulator))} {report : Work Item Accumulator}
    (finished : (answerMachine (core consume)).run fuel (start items accumulator) =
      (events, .finished report)) : report.result = reference consume accumulator items := by
  obtain ⟨otherFuel, otherEvents, otherReport, _, otherFinished, result⟩ :=
    machine_completes consume items accumulator
  have first : (core consume).Produces (items, accumulator) report :=
    (produces_iff_finished (core consume) (items, accumulator) report).mpr ⟨fuel, events, finished⟩
  have second : (core consume).Produces (items, accumulator) otherReport :=
    (produces_iff_finished (core consume) (items, accumulator) otherReport).mpr
      ⟨otherFuel, otherEvents, otherFinished⟩
  exact (congrArg Work.result ((core consume).produces_unique first second)).trans result

end RetainedFold

/-! ## First-order event machines in the shared cursor scheduler -/

namespace EventCursor

open _root_.CategoryTheory Mettapedia.TypeTheory

variable {State Event Verdict Request : Type}

/-- A request inspects one actual machine configuration. Replies preserve
all five transition kinds and absence of a transition. -/
abbrev protocol (State Event Verdict Request : Type) :
    IndexedPolynomial PUnit (fun _ => PUnit) where
  Shape _ _ := State
  Position _ := Option (Transition State Event Verdict Request)
  next _ _ := .unit

def provider (machine : Machine State Event Verdict Request) :
    Cursor.Provider (protocol State Event Verdict Request) where
  State _ _ := PUnit
  step _ configuration := ⟨machine.step configuration, .unit⟩

/-- The retained control is the existing machine outcome and its event
history. The adapter adds no host continuation. An external request stays a
suspended machine outcome; it is never automatically answered by a poll. -/
abbrev Control (State Event Verdict Request : Type) :=
  List Event × Outcome State Verdict Request

def accept (events : List Event) (configuration : State) :
    Option (Transition State Event Verdict Request) → Control State Event Verdict Request
  | none => (events, .stuck configuration)
  | some (.silent next) => (events, .exhausted next)
  | some (.publish added next) => (events ++ added, .exhausted next)
  | some (.finish verdict) => (events, .finished verdict)
  | some (.fail faults) => (events ++ faults, .faulted)
  | some (.call request saved) => (events, .suspended request saved)

def client : Cursor.Client (P := protocol State Event Verdict Request)
    (Return := fun _ _ => Control State Event Verdict Request) where
  V _ _ := Control State Event Verdict Request
  str := fun _ _ => ↾(fun control => match control.2 with
    | .exhausted configuration => ⟨.inr configuration, accept control.1 configuration⟩
    | _ => ⟨.inl control, fun impossible => nomatch impossible⟩)

/-- The charge is the machine's declared transition price. Looking for a
missing transition is uncharged, as in `Machine.spent`; physical polling cost
is not specified by that account. -/
def charge (machine : Machine State Event Verdict Request) (price : State → Nat) :
    Cursor.Charge (provider machine) := fun _ configuration =>
  match machine.step configuration with | none => 0 | some _ => price configuration

abbrev Result (machine : Machine State Event Verdict Request) :=
  Cursor.Outcome (provider machine) client .unit

def packet (machine : Machine State Event Verdict Request)
    (control : Control State Event Verdict Request) : Cursor.Packet (provider machine) client .unit :=
  ⟨.unit, control, .unit⟩

/-- A terminal reply may already be retained when the scheduling allowance
ends. Reading it does not need another machine transition. Cursor `done`
means the client returned; the returned machine outcome still distinguishes
completion, a request, fault and stuckness. -/
def read (machine : Machine State Event Verdict Request) :
    Result machine → Control State Event Verdict Request
  | .paused ⟨.unit, control, .unit⟩ => control
  | .done ⟨.unit, control, .unit⟩ => control

theorem advance_inspect (machine : Machine State Event Verdict Request) (price : State → Nat)
    (fuel : Nat) (configuration : State) (events : List Event) :
    Cursor.advance (provider machine) client (charge machine price) (fuel + 1)
        (packet machine (events, .exhausted configuration)) =
      let rest := Cursor.advance (provider machine) client (charge machine price) fuel
        (packet machine (accept events configuration (machine.step configuration)))
      (charge machine price (base := .unit) (index := .unit) .unit configuration + rest.1, rest.2) := rfl

theorem terminal_read (machine : Machine State Event Verdict Request) (price : State → Nat)
    (fuel : Nat) (events : List Event) (outcome : Outcome State Verdict Request)
    (terminal : ∀ configuration, outcome ≠ .exhausted configuration) :
    (Cursor.advance (provider machine) client (charge machine price)
      fuel (packet machine (events, outcome))).1 = 0 ∧
    read machine (Cursor.advance (provider machine) client (charge machine price)
      fuel (packet machine (events, outcome))).2 = (events, outcome) := by
  cases fuel <;> cases outcome
  all_goals first | exact ⟨rfl, rfl⟩ | exact (terminal _ rfl).elim

/-- Every cursor visit executes the independently defined machine runner
with the same budget, reached configuration and event occurrences. Terminal
client bookkeeping adds no machine transition and no transition charge. -/
theorem advance_run (machine : Machine State Event Verdict Request) (price : State → Nat)
    (fuel : Nat) (configuration : State) (events : List Event) :
    let actual := Cursor.advance (provider machine) client (charge machine price)
      fuel (packet machine (events, .exhausted configuration))
    actual.1 = machine.spent price fuel configuration ∧
      read machine actual.2 =
        (events ++ (machine.run fuel configuration).1, (machine.run fuel configuration).2) := by
  induction fuel generalizing configuration events with
  | zero => simp [Cursor.advance, packet, read, Machine.spent, Machine.run]
  | succ fuel ih =>
      dsimp only
      rw [advance_inspect]
      cases stepped : machine.step configuration with
      | none =>
          have stopped := terminal_read machine price fuel events (.stuck configuration) (by simp)
          simpa [charge, accept, stepped,
            Machine.spent, Machine.run] using stopped
      | some transition =>
          cases transition with
          | silent next =>
              simpa [charge, accept, stepped,
                Machine.spent, Machine.run] using
                And.intro (congrArg (price configuration + ·) (ih next events).1) (ih next events).2
          | publish added next =>
              simpa [charge, accept, stepped,
                Machine.spent, Machine.run, List.append_assoc] using
                And.intro (congrArg (price configuration + ·) (ih next (events ++ added)).1)
                  (ih next (events ++ added)).2
          | finish verdict =>
              have stopped := terminal_read machine price fuel events (.finished verdict) (by simp)
              simpa [charge, accept, stepped,
                Machine.spent, Machine.run, stopped.1] using
                And.intro (congrArg (price configuration + ·) stopped.1) stopped.2
          | fail faults =>
              have stopped := terminal_read machine price fuel (events ++ faults) .faulted (by simp)
              simpa [charge, accept, stepped,
                Machine.spent, Machine.run, stopped.1] using
                And.intro (congrArg (price configuration + ·) stopped.1) stopped.2
          | call request saved =>
              have stopped := terminal_read machine price fuel events (.suspended request saved) (by simp)
              simpa [charge, accept, stepped,
                Machine.spent, Machine.run, stopped.1] using
                And.intro (congrArg (price configuration + ·) stopped.1) stopped.2

/-- Splitting the scheduler allowance preserves the actual first-order
residual, terminal reply and accumulated account, before any readback. -/
theorem advance_split (machine : Machine State Event Verdict Request) (price : State → Nat)
    (earlier later : Nat) (configuration : State) (events : List Event) :
    Cursor.advance (provider machine) client (charge machine price) (earlier + later)
        (packet machine (events, .exhausted configuration)) =
      Cursor.resume (provider machine) client (charge machine price) later
        (Cursor.advance (provider machine) client (charge machine price) earlier
          (packet machine (events, .exhausted configuration))) :=
  Cursor.advance_add _ _ _ _ _ _

/-- A live source cut is the actual paused cursor packet, including its
whole reached configuration. No terminal-client inspection is inserted in
that live prefix. -/
theorem advance_exhausted (machine : Machine State Event Verdict Request) (price : State → Nat)
    (fuel : Nat) (configuration : State) (events : List Event)
    {published : List Event} {saved : State}
    (reached : machine.run fuel configuration = (published, .exhausted saved)) :
    Cursor.advance (provider machine) client (charge machine price) fuel
        (packet machine (events, .exhausted configuration)) =
      (machine.spent price fuel configuration,
        .paused (packet machine (events ++ published, .exhausted saved))) := by
  induction fuel generalizing configuration events published saved with
  | zero =>
      simp only [Machine.run] at reached
      cases reached
      simp [Cursor.advance, packet, Machine.spent]
  | succ fuel ih =>
      rw [advance_inspect]
      cases stepped : machine.step configuration with
      | none => simp [Machine.run, stepped] at reached
      | some transition =>
          cases transition with
          | silent next =>
              have following : machine.run fuel next = (published, .exhausted saved) := by
                simpa only [Machine.run, stepped] using reached
              simp only [accept]
              rw [ih next events following]
              simp [Machine.spent, stepped, charge]
          | publish added next =>
              have publishedRun := reached
              rw [machine.run_succ_publish stepped] at publishedRun
              have following : machine.run fuel next =
                  ((machine.run fuel next).1, .exhausted saved) := by
                have residual : (machine.run fuel next).2 = .exhausted saved :=
                  congrArg Prod.snd publishedRun
                exact Prod.ext rfl residual
              have history : added ++ (machine.run fuel next).1 = published :=
                congrArg Prod.fst publishedRun
              simp only [accept]
              rw [ih next (events ++ added) following]
              simp only [Machine.spent, stepped, charge, List.append_assoc, history]
          | finish verdict => simp [Machine.run, stepped] at reached
          | fail faults => simp [Machine.run, stepped] at reached
          | call request saved => simp [Machine.run, stepped] at reached

/-- An unbounded machine execution remains live for every scheduling
allowance. Silent and reactive divergence are both preserved; fairness is
not imposed by the cursor adapter. -/
theorem divergence_pauses (machine : Machine State Event Verdict Request) (price : State → Nat)
    (configuration : State) (events : List Event) (diverges : machine.DivergesWithin configuration)
    (fuel : Nat) :
    ∃ saved, (Cursor.advance (provider machine) client (charge machine price) fuel
      (packet machine (events, .exhausted configuration))).2 =
        .paused (packet machine (events ++ (machine.run fuel configuration).1, .exhausted saved)) := by
  obtain ⟨saved, unfinished⟩ := diverges fuel
  exact ⟨saved, congrArg Prod.snd (advance_exhausted machine price fuel configuration events
    (Prod.ext rfl unfinished))⟩

section Relational

variable {Source Target SourceEvent TargetEvent SourceVerdict TargetVerdict SourceRequest TargetRequest
  PublicEvent PublicVerdict PublicRequest : Type}
variable (source : Machine Source SourceEvent SourceVerdict SourceRequest)
  {target : Target → Option (Transition Target TargetEvent TargetVerdict TargetRequest) → Prop}
  {related : Source → Target → Prop}
  {sourceRead : ExecutionReadout SourceEvent SourceVerdict SourceRequest PublicEvent PublicVerdict PublicRequest}
  {targetRead : ExecutionReadout TargetEvent TargetVerdict TargetRequest PublicEvent PublicVerdict PublicRequest}

/-- Scheduling an executable realization preserves its declared relational
observation, including incomplete and suspended endpoints. Only newly executed
target blocks contribute new events; the existing public history is retained.
The scheduler account is the source machine's account, with no assumed ratio
between source inspections and target work. -/
theorem advance_simulation
    (simulation : DerivationSimulation (fun state action => source.step state = action)
      target related sourceRead targetRead)
    (price : Source → Nat) (fuel : Nat) (history : List SourceEvent)
    {state : Source} {state' : Target} (retained : related state state') :
    let actual := Cursor.advance (provider source) client (charge source price) fuel
      (packet source (history, .exhausted state))
    actual.1 = source.spent price fuel state ∧
      ∃ count events' outcome', Derivation target count state' events' outcome' ∧
        (read source actual.2).1.flatMap sourceRead.event =
          history.flatMap sourceRead.event ++ events'.flatMap targetRead.event ∧
        OutcomeRel related ((read source actual.2).2.relabel sourceRead.verdict sourceRead.request)
          (outcome'.relabel targetRead.verdict targetRead.request) := by
  have executed := advance_run source price fuel state history
  obtain ⟨count, events', outcome', path, publicEvents, publicOutcome⟩ :=
    source.run_related_to_rule simulation fuel retained
  refine ⟨executed.1, count, events', outcome', path, ?_, ?_⟩
  · rw [executed.2, List.flatMap_append, publicEvents]
  · rw [executed.2]
    exact publicOutcome

/-- A live scheduler cut and its relational realization resume at their
actual reached configurations. The target prefix is constructed once; the
suffix starts at its saved endpoint and appends only new public events.
Requests, faults and completion remain distinct from an exhausted allowance. -/
theorem resume_simulation
    (simulation : DerivationSimulation (fun state action => source.step state = action)
      target related sourceRead targetRead)
    (price : Source → Nat) (earlier later : Nat) (history : List SourceEvent)
    {state saved : Source} {published : List SourceEvent}
    (cut : source.run earlier state = (published, .exhausted saved))
    {state' : Target} (retained : related state state') :
    let actual := Cursor.resume (provider source) client (charge source price) later
      (Cursor.advance (provider source) client (charge source price) earlier
        (packet source (history, .exhausted state)))
    actual.1 = source.spent price earlier state + source.spent price later saved ∧
      ∃ first second saved' events' later' outcome',
        Derivation target first state' events' (.exhausted saved') ∧
        related saved saved' ∧ Derivation target second saved' later' outcome' ∧
        events'.flatMap targetRead.event = published.flatMap sourceRead.event ∧
        (read source actual.2).1.flatMap sourceRead.event =
          history.flatMap sourceRead.event ++ (events' ++ later').flatMap targetRead.event ∧
        OutcomeRel related ((read source actual.2).2.relabel sourceRead.verdict sourceRead.request)
          (outcome'.relabel targetRead.verdict targetRead.request) ∧
        Derivation target (first + second) state' (events' ++ later') outcome' := by
  have prefixPath := source.execution_derivation earlier state
  rw [cut] at prefixPath
  obtain ⟨first, second, saved', events', later', outcome', prefixPath', suffixPath,
      savedRelated, prefixRead, suffixRead, outcomeRelated, whole⟩ :=
    simulation.resume prefixPath (source.execution_derivation later saved) retained
  have reached := advance_exhausted source price earlier state history cut
  have continued := advance_run source price later saved (history ++ published)
  dsimp only
  rw [reached]
  change _ + _ = _ ∧ _
  refine ⟨congrArg (source.spent price earlier state + ·) continued.1,
    first, second, saved', events', later', outcome', prefixPath', savedRelated, suffixPath, prefixRead, ?_, ?_, whole⟩
  · change (read source (Cursor.advance (provider source) client (charge source price) later
      (packet source (history ++ published, .exhausted saved))).2).1.flatMap sourceRead.event = _
    rw [continued.2]
    simp only [List.flatMap_append, prefixRead, suffixRead, List.append_assoc]
  · change OutcomeRel related
      ((read source (Cursor.advance (provider source) client (charge source price) later
        (packet source (history ++ published, .exhausted saved))).2).2.relabel _ _) _
    rw [continued.2]
    exact outcomeRelated

end Relational

/-- When both local rules have executable realizations, the related endpoints
are actual cursor results on both sides. The target receives its own finite
allowance and price; equality of public observations imposes neither identical
instruction schedules nor equal resource accounts. -/
theorem advance_machines
    {Source Target SourceEvent TargetEvent SourceVerdict TargetVerdict SourceRequest TargetRequest
      PublicEvent PublicVerdict PublicRequest : Type}
    (source : Machine Source SourceEvent SourceVerdict SourceRequest)
    (target : Machine Target TargetEvent TargetVerdict TargetRequest)
    {related : Source → Target → Prop}
    {sourceRead : ExecutionReadout SourceEvent SourceVerdict SourceRequest PublicEvent PublicVerdict PublicRequest}
    {targetRead : ExecutionReadout TargetEvent TargetVerdict TargetRequest PublicEvent PublicVerdict PublicRequest}
    (simulation : DerivationSimulation (fun state action => source.step state = action)
      (fun state action => target.step state = action) related sourceRead targetRead)
    (sourcePrice : Source → Nat) (targetPrice : Target → Nat) (fuel : Nat)
    {state : Source} {state' : Target} (retained : related state state') :
    ∃ count,
      let first := Cursor.advance (provider source) client (charge source sourcePrice) fuel
        (packet source ([], .exhausted state))
      let second := Cursor.advance (provider target) client (charge target targetPrice) count
        (packet target ([], .exhausted state'))
      first.1 = source.spent sourcePrice fuel state ∧
      second.1 = target.spent targetPrice count state' ∧
      (read source first.2).1.flatMap sourceRead.event = (read target second.2).1.flatMap targetRead.event ∧
      OutcomeRel related ((read source first.2).2.relabel sourceRead.verdict sourceRead.request)
        ((read target second.2).2.relabel targetRead.verdict targetRead.request) := by
  obtain ⟨account, count, events', outcome', path, publicEvents, publicOutcome⟩ :=
    advance_simulation source simulation sourcePrice fuel [] retained
  have reached := Derivation.sound target (fun _ _ step => step) path
  have executed := advance_run target targetPrice count state' []
  rw [reached] at executed
  refine ⟨count, account, executed.1, ?_, ?_⟩
  · rw [executed.2]
    simpa only [List.nil_append, List.flatMap_nil] using publicEvents
  · rw [executed.2]
    exact publicOutcome

namespace Controls

def effectful : Machine (Nat × List String) Nat (List String) String where
  step state := match state.1 with
    | 0 => some (.silent (1, state.2 ++ ["write"]))
    | 1 => some (.publish [7, 7] (2, state.2))
    | 2 => some (.call "lookup" (3, state.2))
    | 3 => some (.finish state.2)
    | _ => none

def initial : Cursor.Packet (provider effectful) client .unit :=
  packet effectful ([], .exhausted (0, []))

def first := Cursor.advance (provider effectful) client (charge effectful (fun _ => 1)) 1 initial

def requested := Cursor.resume (provider effectful) client (charge effectful (fun _ => 1)) 2 first

theorem pause_retains_reached_world :
    first.1 = 1 ∧ read effectful first.2 = ([], .exhausted (1, ["write"])) := by
  exact ⟨rfl, rfl⟩

theorem resumed_keeps_duplicates_and_request :
    requested.1 = 3 ∧
      read effectful requested.2 = ([7, 7], .suspended "lookup" (3, ["write"])) := by
  exact ⟨rfl, rfl⟩

theorem allowance_does_not_answer_request :
    let later := Cursor.resume (provider effectful) client (charge effectful (fun _ => 1)) 20 requested
    later.1 = 3 ∧ read effectful later.2 = ([7, 7], .suspended "lookup" (3, ["write"])) := by
  exact ⟨rfl, rfl⟩

theorem restart_repeats_effect :
    read effectful (Cursor.advance (provider effectful) client (charge effectful (fun _ => 1)) 1
      (packet effectful ([], .exhausted (0, ["write"])))).2 =
        ([], .exhausted (1, ["write", "write"])) ∧
      read effectful first.2 ≠ ([], .exhausted (1, ["write", "write"])) := by
  refine ⟨rfl, ?_⟩
  intro same
  have states := Outcome.exhausted.inj (congrArg Prod.snd same)
  have lengths := congrArg (fun state : Nat × List String => state.2.length) states
  simp at lengths

end Controls

end EventCursor

end Mettapedia.Machines.ProductiveCoreAdapters
