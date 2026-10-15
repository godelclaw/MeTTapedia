import Mettapedia.OSLF.MeTTaIL.GeneralPremiseScheduler

/-!
# Finite expansion trees for the actual premise scheduler

Each branch lists exactly the children produced by the real transition.
Its work account therefore gives a drain bound for any agenda and preserves
the scheduler's complete answer and obligation histories. Concrete execution
machines construct these trees from their checked syntax and child strata.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

variable {Task Answer Obligation : Type}

mutual
  inductive TaskTree (expand : Task → Expansion Task Answer Obligation) : Task → Type where
    | branch {task : Task} (children : TaskForest expand (expand task).tasks) : TaskTree expand task

  inductive TaskForest (expand : Task → Expansion Task Answer Obligation) : List Task → Type where
    | nil : TaskForest expand []
    | cons {task : Task} {tasks : List Task} (head : TaskTree expand task)
        (tail : TaskForest expand tasks) : TaskForest expand (task :: tasks)
end

mutual
  def TaskTree.cost {expand : Task → Expansion Task Answer Obligation} {task : Task} :
      TaskTree expand task → Nat
    | .branch children => children.cost + 1

  def TaskForest.cost {expand : Task → Expansion Task Answer Obligation} {tasks : List Task} :
      TaskForest expand tasks → Nat
    | .nil => 0
    | .cons head tail => head.cost + tail.cost
end

def TaskForest.append {expand : Task → Expansion Task Answer Obligation} {first second : List Task}
    (front : TaskForest expand first) (back : TaskForest expand second) : TaskForest expand (first ++ second) :=
  match front with
  | .nil => back
  | .cons head tail => .cons head (tail.append back)

theorem TaskForest.append_cost {expand : Task → Expansion Task Answer Obligation} {first second : List Task}
    (front : TaskForest expand first) (back : TaskForest expand second) :
    (front.append back).cost = front.cost + back.cost := by
  cases front with
  | nil => simp only [TaskForest.append, TaskForest.cost, Nat.zero_add]
  | cons head tail =>
    simp only [TaskForest.append, TaskForest.cost, append_cost tail back, Nat.add_assoc]
termination_by structural front

def forestOfTrees (expand : Task → Expansion Task Answer Obligation) (tasks : List Task)
    (each : ∀ task, task ∈ tasks → TaskTree expand task) : TaskForest expand tasks :=
  match tasks with
  | [] => .nil
  | task :: tasks => .cons (each task (by simp))
      (forestOfTrees expand tasks (fun child present => each child (by simp [present])))

def advanceTasks (expand : Task → Expansion Task Answer Obligation) : List Task → List Task
  | [] => []
  | task :: tasks => (expand task).tasks ++ tasks

theorem tick_agenda (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) :
    (tick expand state).agenda = advanceTasks expand state.agenda := by
  cases agenda : state.agenda <;> simp only [tick, agenda, advanceTasks]

def TaskForest.advanceAgenda {expand : Task → Expansion Task Answer Obligation} {tasks : List Task}
    (forest : TaskForest expand tasks) : TaskForest expand (advanceTasks expand tasks) :=
  match forest with
  | .nil => .nil
  | .cons (.branch children) tail => children.append tail

theorem TaskForest.advanceAgenda_cost {expand : Task → Expansion Task Answer Obligation} {tasks : List Task}
    (forest : TaskForest expand tasks) (pending : tasks ≠ []) :
    forest.advanceAgenda.cost + 1 = forest.cost := by
  cases forest with
  | nil => exact False.elim (pending rfl)
  | cons head tail =>
    cases head with
    | branch children =>
      change (children.append tail).cost + 1 = children.cost + 1 + tail.cost
      rw [TaskForest.append_cost]
      omega

theorem TaskForest.cost_cast {expand : Task → Expansion Task Answer Obligation} {first second : List Task}
    (same : first = second) (forest : TaskForest expand first) : (same ▸ forest).cost = forest.cost := by
  cases same
  rfl

def TaskForest.advance {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    TaskForest expand (tick expand state).agenda :=
  (tick_agenda expand state).symm ▸ forest.advanceAgenda

theorem TaskForest.advance_cost {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (pending : state.agenda ≠ []) :
    (forest.advance state).cost + 1 = forest.cost := by
  simp only [TaskForest.advance, TaskForest.cost_cast]
  exact forest.advanceAgenda_cost pending

theorem run_idle (expand : Task → Expansion Task Answer Obligation) (fuel : Nat)
    (state : State Task Answer Obligation) (idle : state.agenda = []) : run expand fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, tick_idle expand state idle] using ih

theorem finiteWork_drains (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (sufficient : forest.cost ≤ fuel) : (run expand fuel state).agenda = [] := by
  induction fuel generalizing state with
  | zero =>
    cases state with
    | mk agenda answers unresolved work =>
      cases agenda with
      | nil => rfl
      | cons task tasks =>
        cases forest with
        | cons head tail =>
          cases head with
          | branch children => simp only [TaskForest.cost, TaskTree.cost] at sufficient; omega
  | succ fuel ih =>
    by_cases pending : state.agenda = []
    · rw [run_idle expand (fuel + 1) state pending]
      exact pending
    · have decrease := forest.advance_cost state pending
      exact ih (tick expand state) (forest.advance state) (by omega)

theorem finiteWork_eventually_settled (expand : Task → Expansion Task Answer Obligation)
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    ∃ fuel, settled (run expand fuel state) = true :=
  ⟨forest.cost, by simp only [settled, finiteWork_drains expand forest.cost state forest (Nat.le_refl _),
    List.isEmpty_nil]⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler
