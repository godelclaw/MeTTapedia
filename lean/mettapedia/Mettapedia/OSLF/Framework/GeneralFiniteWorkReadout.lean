import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFiniteWork

/-!
# Exact answer and obligation readouts of finite scheduler work

The expansion tree records the actual children of each microstep. Draining
its work account appends every answer and unresolved obligation in scheduler
order. No answer list or completeness assertion is supplied to the tree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

variable {Task Answer Obligation : Type}

mutual
  def TaskTree.answers {expand : Task → Expansion Task Answer Obligation} {task : Task} :
      TaskTree expand task → List Answer
    | .branch children => (expand task).answers ++ children.answers

  def TaskForest.answers {expand : Task → Expansion Task Answer Obligation} {tasks : List Task} :
      TaskForest expand tasks → List Answer
    | .nil => []
    | .cons head tail => head.answers ++ tail.answers
end

mutual
  def TaskTree.obligations {expand : Task → Expansion Task Answer Obligation} {task : Task} :
      TaskTree expand task → List Obligation
    | .branch children => (expand task).unresolved ++ children.obligations

  def TaskForest.obligations {expand : Task → Expansion Task Answer Obligation} {tasks : List Task} :
      TaskForest expand tasks → List Obligation
    | .nil => []
    | .cons head tail => head.obligations ++ tail.obligations
end

theorem TaskForest.append_answers {expand : Task → Expansion Task Answer Obligation}
    {first second : List Task} (front : TaskForest expand first) (back : TaskForest expand second) :
    (front.append back).answers = front.answers ++ back.answers := by
  cases front with
  | nil => simp only [TaskForest.append, TaskForest.answers, List.nil_append]
  | cons head tail =>
      simp only [TaskForest.append, TaskForest.answers, append_answers tail back, List.append_assoc]
termination_by structural front

theorem TaskForest.append_obligations {expand : Task → Expansion Task Answer Obligation}
    {first second : List Task} (front : TaskForest expand first) (back : TaskForest expand second) :
    (front.append back).obligations = front.obligations ++ back.obligations := by
  cases front with
  | nil => simp only [TaskForest.append, TaskForest.obligations, List.nil_append]
  | cons head tail =>
      simp only [TaskForest.append, TaskForest.obligations, append_obligations tail back, List.append_assoc]
termination_by structural front

theorem TaskForest.answers_cast {expand : Task → Expansion Task Answer Obligation}
    {first second : List Task} (same : first = second) (forest : TaskForest expand first) :
    (same ▸ forest).answers = forest.answers := by cases same; rfl

theorem TaskForest.obligations_cast {expand : Task → Expansion Task Answer Obligation}
    {first second : List Task} (same : first = second) (forest : TaskForest expand first) :
    (same ▸ forest).obligations = forest.obligations := by cases same; rfl

theorem TaskForest.advance_answers {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    (tick expand state).answers ++ (forest.advance state).answers = state.answers ++ forest.answers := by
  simp only [TaskForest.advance, TaskForest.answers_cast]
  cases state with
  | mk agenda answers unresolved work =>
      cases forest with
      | nil => rfl
      | cons head tail =>
          cases head with
          | branch children =>
              simp only [tick, TaskForest.advanceAgenda, advanceTasks,
                TaskForest.answers, TaskTree.answers, List.append_assoc]
              rw [TaskForest.append_answers children tail]

theorem TaskForest.advance_obligations {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    (tick expand state).unresolved ++ (forest.advance state).obligations =
      state.unresolved ++ forest.obligations := by
  simp only [TaskForest.advance, TaskForest.obligations_cast]
  cases state with
  | mk agenda answers unresolved work =>
      cases forest with
      | nil => rfl
      | cons head tail =>
          cases head with
          | branch children =>
              simp only [tick, TaskForest.advanceAgenda, advanceTasks,
                TaskForest.obligations, TaskTree.obligations, List.append_assoc]
              rw [TaskForest.append_obligations children tail]

theorem TaskForest.answers_empty {expand : Task → Expansion Task Answer Obligation}
    {tasks : List Task} (forest : TaskForest expand tasks) (empty : tasks = []) :
    forest.answers = [] := by
  subst tasks
  cases forest
  rfl

theorem TaskForest.obligations_empty {expand : Task → Expansion Task Answer Obligation}
    {tasks : List Task} (forest : TaskForest expand tasks) (empty : tasks = []) :
    forest.obligations = [] := by
  subst tasks
  cases forest
  rfl

theorem finiteWork_readouts (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda)
    (sufficient : forest.cost ≤ fuel) :
    (run expand fuel state).answers = state.answers ++ forest.answers ∧
      (run expand fuel state).unresolved = state.unresolved ++ forest.obligations := by
  induction fuel generalizing state with
  | zero =>
      have empty := finiteWork_drains expand 0 state forest sufficient
      change state.agenda = [] at empty
      simp only [run, forest.answers_empty empty, forest.obligations_empty empty,
        List.append_nil, and_self]
  | succ fuel ih =>
      by_cases empty : state.agenda = []
      · rw [run_idle expand (fuel + 1) state empty]
        simp only [forest.answers_empty empty, forest.obligations_empty empty,
          List.append_nil, and_self]
      · have decrease := forest.advance_cost state empty
        have next := ih (tick expand state) (forest.advance state) (by omega)
        change (run expand fuel (tick expand state)).answers = _ ∧
          (run expand fuel (tick expand state)).unresolved = _
        exact ⟨next.1.trans (forest.advance_answers state),
          next.2.trans (forest.advance_obligations state)⟩

theorem settled_run_unique (expand : Task → Expansion Task Answer Obligation)
    (initial : State Task Answer Obligation) (first second : Nat)
    (firstIdle : (run expand first initial).agenda = [])
    (secondIdle : (run expand second initial).agenda = []) :
    run expand first initial = run expand second initial := by
  rcases Nat.le_total first second with before | before
  · obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le before
    rw [same, run_add, run_idle expand extra _ firstIdle]
  · obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le before
    rw [same, run_add, run_idle expand extra _ secondIdle]

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler
