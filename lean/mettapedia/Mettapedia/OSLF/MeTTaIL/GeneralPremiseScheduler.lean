import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Exact resumption of explicit premise work

A transition advances one retained work frame. Successful answers and
unresolved admission obligations are append-only. Fuel exhaustion leaves the
remaining frames in the state; only an empty agenda without obligations is
complete. The scheduler is shared by query, quantifier and child frames.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

structure Expansion (Task Answer Obligation : Type) where
  tasks : List Task := []
  answers : List Answer := []
  unresolved : List Obligation := []

structure State (Task Answer Obligation : Type) where
  agenda : List Task := []
  answers : List Answer := []
  unresolved : List Obligation := []
  work : Nat := 0

variable {Task Answer Obligation : Type}

def tick (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) : State Task Answer Obligation :=
  match state.agenda with
  | [] => state
  | task :: tasks =>
      let next := expand task
      { agenda := next.tasks ++ tasks
        answers := state.answers ++ next.answers
        unresolved := state.unresolved ++ next.unresolved
        work := state.work + 1 }

def run (expand : Task → Expansion Task Answer Obligation) :
    Nat → State Task Answer Obligation → State Task Answer Obligation
  | 0, state => state
  | fuel + 1, state => run expand fuel (tick expand state)

def complete (state : State Task Answer Obligation) : Bool :=
  state.agenda.isEmpty && state.unresolved.isEmpty

def settled (state : State Task Answer Obligation) : Bool := state.agenda.isEmpty

@[simp] theorem run_zero (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) : run expand 0 state = state := rfl

@[simp] theorem tick_idle (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) (idle : state.agenda = []) :
    tick expand state = state := by simp [tick, idle]

theorem run_add (expand : Task → Expansion Task Answer Obligation)
    (first second : Nat) (state : State Task Answer Obligation) :
    run expand (first + second) state = run expand second (run expand first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first inductionHypothesis =>
      simpa only [Nat.succ_add, run] using inductionHypothesis (tick expand state)

/-- Prefix means that complete values and their origins remain in their
original order, rather than merely preserving an endpoint set. -/
def Prefix {α : Type} (front back : List α) : Prop := ∃ tail, back = front ++ tail

theorem Prefix.refl {α : Type} (items : List α) : Prefix items items := ⟨[], by simp⟩

theorem Prefix.trans {α : Type} {first second third : List α}
    (front : Prefix first second) (back : Prefix second third) : Prefix first third := by
  obtain ⟨middle, rfl⟩ := front
  obtain ⟨tail, rfl⟩ := back
  exact ⟨middle ++ tail, by simp only [List.append_assoc]⟩

theorem tick_answers_prefix (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) : Prefix state.answers (tick expand state).answers := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using Prefix.refl state.answers
  | cons task tasks => exact ⟨(expand task).answers, by simp [tick, agenda]⟩

theorem tick_obligations_prefix (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) :
    Prefix state.unresolved (tick expand state).unresolved := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using Prefix.refl state.unresolved
  | cons task tasks => exact ⟨(expand task).unresolved, by simp [tick, agenda]⟩

theorem run_answers_prefix (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) :
    Prefix state.answers (run expand fuel state).answers := by
  induction fuel generalizing state with
  | zero => exact Prefix.refl _
  | succ fuel inductionHypothesis =>
      exact (tick_answers_prefix expand state).trans (inductionHypothesis (tick expand state))

theorem run_obligations_prefix (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) :
    Prefix state.unresolved (run expand fuel state).unresolved := by
  induction fuel generalizing state with
  | zero => exact Prefix.refl _
  | succ fuel inductionHypothesis =>
      exact (tick_obligations_prefix expand state).trans (inductionHypothesis (tick expand state))

theorem tick_work_bounds (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) :
    state.work ≤ (tick expand state).work ∧ (tick expand state).work ≤ state.work + 1 := by
  cases agenda : state.agenda <;> simp [tick, agenda]

theorem run_work_bounds (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) :
    state.work ≤ (run expand fuel state).work ∧
      (run expand fuel state).work ≤ state.work + fuel := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel inductionHypothesis =>
      have step := tick_work_bounds expand state
      have tail := inductionHypothesis (tick expand state)
      constructor
      · exact step.1.trans tail.1
      · change (run expand fuel (tick expand state)).work ≤ state.work + (fuel + 1)
        omega

def spent (expand : Task → Expansion Task Answer Obligation) (fuel : Nat)
    (state : State Task Answer Obligation) : Nat :=
  (run expand fuel state).work - state.work

theorem spent_add (expand : Task → Expansion Task Answer Obligation)
    (first second : Nat) (state : State Task Answer Obligation) :
    spent expand (first + second) state = spent expand first state +
      spent expand second (run expand first state) := by
  unfold spent
  rw [run_add]
  have front := (run_work_bounds expand first state).1
  have back := (run_work_bounds expand second (run expand first state)).1
  omega

theorem complete_iff (state : State Task Answer Obligation) :
    complete state = true ↔ state.agenda = [] ∧ state.unresolved = [] := by
  simp [complete]

theorem unresolved_not_complete (state : State Task Answer Obligation)
    (unresolved : state.unresolved ≠ []) : complete state = false := by
  cases completed : complete state with
  | false => rfl
  | true => exact False.elim (unresolved ((complete_iff state).mp completed).2)

theorem pending_not_complete (state : State Task Answer Obligation)
    (pending : state.agenda ≠ []) : complete state = false := by
  cases completed : complete state with
  | false => rfl
  | true => exact False.elim (pending ((complete_iff state).mp completed).1)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

open Mettapedia.OSLF.MeTTaIL.GeneralPremise

theorem tick_preserves {Task Answer Obligation : Type}
    (taskCovered : Task → Prop) (answerCovered : Answer → Prop)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (preserved : ∀ task, taskCovered task →
      (∀ next ∈ (expand task).tasks, taskCovered next) ∧
      (∀ answer ∈ (expand task).answers, answerCovered answer))
    (state : Scheduler.State Task Answer Obligation)
    (covered : (∀ task ∈ state.agenda, taskCovered task) ∧
      (∀ answer ∈ state.answers, answerCovered answer)) :
    (∀ task ∈ (Scheduler.tick expand state).agenda, taskCovered task) ∧
    (∀ answer ∈ (Scheduler.tick expand state).answers, answerCovered answer) := by
  cases agenda : state.agenda with
  | nil => simpa only [Scheduler.tick, agenda] using covered
  | cons task tasks =>
      have next := preserved task (covered.1 task (by rw [agenda]; simp))
      constructor
      · intro item member
        simp only [Scheduler.tick, agenda, List.mem_append] at member
        rcases member with member | member
        · exact next.1 item member
        · exact covered.1 item (by rw [agenda]; exact List.mem_cons_of_mem _ member)
      · intro item member
        simp only [Scheduler.tick, agenda, List.mem_append] at member
        rcases member with member | member
        · exact covered.2 item member
        · exact next.2 item member

theorem run_preserves {Task Answer Obligation : Type}
    (taskCovered : Task → Prop) (answerCovered : Answer → Prop)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (preserved : ∀ task, taskCovered task →
      (∀ next ∈ (expand task).tasks, taskCovered next) ∧
      (∀ answer ∈ (expand task).answers, answerCovered answer))
    (fuel : Nat) (state : Scheduler.State Task Answer Obligation)
    (covered : (∀ task ∈ state.agenda, taskCovered task) ∧
      (∀ answer ∈ state.answers, answerCovered answer)) :
    (∀ task ∈ (Scheduler.run expand fuel state).agenda, taskCovered task) ∧
    (∀ answer ∈ (Scheduler.run expand fuel state).answers, answerCovered answer) := by
  induction fuel generalizing state with
  | zero => exact covered
  | succ fuel ih =>
      exact ih (Scheduler.tick expand state)
        (tick_preserves taskCovered answerCovered expand preserved state covered)

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler.tick_preserves
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler.run_preserves

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler
