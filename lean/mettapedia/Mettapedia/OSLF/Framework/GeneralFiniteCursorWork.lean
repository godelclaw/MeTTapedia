import Mettapedia.OSLF.Framework.GeneralFiniteWorkReadout

/-!
# Residual work and answer-cursor accounting

The forest is proof infrastructure for actual scheduler expansions. Ordinary
microsteps do not construct it. Its residual readouts account for answers
already emitted and answers still in the exact pending work tree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

variable {Task Answer Obligation : Type}

def TaskForest.afterRun {expand : Task → Expansion Task Answer Obligation}
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    TaskForest expand (run expand fuel state).agenda :=
  match fuel with
  | 0 => forest
  | fuel + 1 => (forest.advance state).afterRun fuel (tick expand state)

theorem TaskForest.afterRun_answers {expand : Task → Expansion Task Answer Obligation}
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    (run expand fuel state).answers ++ (forest.afterRun fuel state).answers =
      state.answers ++ forest.answers := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, TaskForest.afterRun]
      exact (ih (tick expand state) (forest.advance state)).trans (forest.advance_answers state)

theorem TaskForest.afterRun_obligations {expand : Task → Expansion Task Answer Obligation}
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    (run expand fuel state).unresolved ++ (forest.afterRun fuel state).obligations =
      state.unresolved ++ forest.obligations := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, TaskForest.afterRun]
      exact (ih (tick expand state) (forest.advance state)).trans (forest.advance_obligations state)

/-- Answer delivery can schedule a fixed number of outer administrative tasks.
The scale pays for those tasks without treating them as primitive events. -/
def TaskForest.cursorDebt {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (cursor scale : Nat) : Nat :=
  forest.cost + scale * (state.answers.length + forest.answers.length - cursor) + 1

theorem TaskForest.cursorDebt_cursor {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (cursor scale : Nat) (answer : Answer) (found : state.answers[cursor]? = some answer) :
    forest.cursorDebt state (cursor + 1) scale + scale = forest.cursorDebt state cursor scale := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  have decrement : state.answers.length + forest.answers.length - cursor =
      (state.answers.length + forest.answers.length - (cursor + 1)) + 1 := by omega
  simp only [TaskForest.cursorDebt]
  rw [decrement, Nat.mul_add, Nat.mul_one]
  omega

theorem TaskForest.cursorDebt_tick {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (cursor scale : Nat) (pending : state.agenda ≠ []) :
    (forest.advance state).cursorDebt (tick expand state) cursor scale + 1 =
      forest.cursorDebt state cursor scale := by
  have decrease := forest.advance_cost state pending
  have total := congrArg List.length (forest.advance_answers state)
  simp only [List.length_append] at total
  simp only [TaskForest.cursorDebt]
  rw [total]
  omega

theorem TaskForest.cursorDebt_positive {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (cursor scale : Nat) : 0 < forest.cursorDebt state cursor scale := by
  simp only [TaskForest.cursorDebt]
  omega

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler
