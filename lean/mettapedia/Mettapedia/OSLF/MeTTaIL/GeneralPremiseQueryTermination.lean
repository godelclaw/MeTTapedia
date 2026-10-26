import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQuery
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination

/-!
# Structural drainage of interrupted finite queries

Provider rows and query arguments are finite. Matcher continuations use an
independently proved cursor cost. The existing lexicographic expansion rank
and finite task-tree cost then establish drainage for the actual retained
query machine, including dynamic input and acquired-row frames.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching

variable {matcher : MatchingExecution}

abbrev Rank := Nat × (Nat × Nat)

def Task.rank (cost : matcher.CursorCost) (environment : Environment) (request : Request) :
    Task environment request matcher → Rank
  | .start => (5, 0, 0)
  | .rows frame => (3, environment.provider.rows.length - frame.cursor, 0)
  | .dynamicInputs frame => (4, frame.schemas.length, 0)
  | .dynamicRows frame => (3, frame.rows.length - frame.cursor, 0)
  | .arguments frame => (2, 2 * frame.schemas.length + 1, 0)
  | .matcher frame => (2, 2 * frame.schemas.length + 2,
      cost.debt frame.query frame.state frame.cursor)

abbrev RankSmaller : Rank → Rank → Prop :=
  Prod.Lex ((· < ·) : Nat → Nat → Prop)
    (Prod.Lex ((· < ·) : Nat → Nat → Prop) ((· < ·) : Nat → Nat → Prop))

private theorem phase_smaller (phase other : Nat) (left right : Nat × Nat)
    (smaller : phase < other) : RankSmaller (phase, left) (other, right) :=
  Prod.Lex.left _ _ smaller

private theorem count_smaller (phase before after beforeDebt afterDebt : Nat)
    (smaller : before < after) :
    RankSmaller (phase, before, beforeDebt) (phase, after, afterDebt) :=
  Prod.Lex.right _ (Prod.Lex.left _ _ smaller)

private theorem debt_smaller (phase count before after : Nat)
    (smaller : before < after) :
    RankSmaller (phase, count, before) (phase, count, after) :=
  Prod.Lex.right _ (Prod.Lex.right _ smaller)

theorem expandArguments_decreases (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request matcher) (branch : Task environment request matcher)
    (member : branch ∈ (expandArguments environment request frame).tasks) :
    RankSmaller (Task.rank cost environment request branch)
      (Task.rank cost environment request (.arguments frame)) := by
  unfold expandArguments at member
  split at member
  · split at member <;> simp at member
  · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
    cases mode with
    | input =>
      dsimp only at member
      split at member
      · simp at member
      · split at member
        · simp only [List.mem_singleton] at member
          subst branch
          apply count_smaller
          dsimp only
          simp only [schemasFound, List.length_cons]
          omega
        · simp at member
    | output =>
      dsimp only at member
      simp only [List.mem_singleton] at member
      subst branch
      apply count_smaller
      dsimp only
      simp only [schemasFound, List.length_cons]
      omega
  · simp at member

theorem expandMatcher_decreases (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request matcher) (branch : Task environment request matcher)
    (member : branch ∈ (expandMatcher environment request frame).tasks) :
    RankSmaller (Task.rank cost environment request branch)
      (Task.rank cost environment request (.matcher frame)) := by
  unfold expandMatcher at member
  split at member
  · rename_i answer found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst branch
    · apply count_smaller
      dsimp only [Task.rank]
      omega
    · apply debt_smaller
      exact cost.consume frame.reachable found
  · rename_i found
    split at member
    · simp at member
    · rename_i pending
      have incomplete : matcher.complete frame.state = false := Bool.eq_false_iff.mpr pending
      simp only [List.mem_singleton] at member
      subst branch
      apply debt_smaller
      exact cost.tick frame.reachable found incomplete

theorem expandDynamicInputs_decreases (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (frame : DynamicInputsFrame environment request) (branch : Task environment request matcher)
    (member : branch ∈ (expandDynamicInputs environment request frame matcher).tasks) :
    RankSmaller (Task.rank cost environment request branch) (Task.rank cost environment request (.dynamicInputs frame)) := by
  unfold expandDynamicInputs at member
  split at member
  · split at member
    · simp at member
    · simp only [List.mem_singleton] at member
      subst branch
      exact phase_smaller 3 4 _ _ (by omega)
  · rename_i schema schemas modes schemasFound modesFound
    split at member
    · simp at member
    · simp only [List.mem_singleton] at member
      subst branch
      apply count_smaller
      dsimp only
      simp only [schemasFound, List.length_cons]
      omega
  · rename_i schema schemas modes schemasFound modesFound
    simp only [List.mem_singleton] at member
    subst branch
    apply count_smaller
    dsimp only
    simp only [schemasFound, List.length_cons]
    omega
  · simp at member

theorem expandDynamicRows_decreases (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (branch : Task environment request matcher)
    (member : branch ∈ (expandDynamicRows environment request frame matcher).tasks) :
    RankSmaller (Task.rank cost environment request branch) (Task.rank cost environment request (.dynamicRows frame)) := by
  unfold expandDynamicRows at member
  split at member
  · simp at member
  · rename_i values found
    have within := (List.getElem?_eq_some_iff.mp found).1
    split at member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst branch
      · exact phase_smaller 2 3 _ _ (by omega)
      · apply count_smaller
        dsimp only
        omega
    · simp only [List.mem_singleton] at member
      subst branch
      apply count_smaller
      dsimp only
      omega

theorem expand_decreases (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (task branch : Task environment request matcher)
    (member : branch ∈ (expand environment request task).tasks) :
    RankSmaller (Task.rank cost environment request branch) (Task.rank cost environment request task) := by
  cases task with
  | start =>
      simp only [expand] at member
      split at member
      · simp at member
      · split at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same <;> subst branch
          · exact phase_smaller 3 5 _ _ (by omega)
          · exact phase_smaller 4 5 _ _ (by omega)
        · simp only [List.mem_singleton] at member
          subst branch
          exact phase_smaller 3 5 _ _ (by omega)
  | rows frame =>
      simp only [expand] at member
      split at member
      · simp at member
      · rename_i row found
        have within := (List.getElem?_eq_some_iff.mp found).1
        split at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same <;> subst branch
          · exact phase_smaller 2 3 _ _ (by omega)
          · apply count_smaller
            dsimp only
            omega
        · simp only [List.mem_singleton] at member
          subst branch
          apply count_smaller
          dsimp only
          omega
  | dynamicInputs frame => exact expandDynamicInputs_decreases cost _ _ _ _ member
  | dynamicRows frame => exact expandDynamicRows_decreases cost _ _ _ _ member
  | arguments frame => exact expandArguments_decreases cost _ _ _ _ member
  | matcher frame => exact expandMatcher_decreases cost _ _ _ _ member

def taskCost (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (task : Task environment request matcher) : Nat :=
  1 + (((expand environment request task).tasks.attach.map fun branch =>
    taskCost cost environment request branch.val).sum)
termination_by Task.rank cost environment request task
decreasing_by exact expand_decreases cost environment request task branch.val branch.property

def agendaCost (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (agenda : List (Task environment request matcher)) : Nat :=
  (agenda.map (taskCost cost environment request)).sum

theorem taskCost_eq (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (task : Task environment request matcher) :
    taskCost cost environment request task =
      1 + agendaCost cost environment request (expand environment request task).tasks := by
  rw [taskCost.eq_def]
  have same := congrArg (fun agenda : List (Task environment request matcher) =>
      (agenda.map (taskCost cost environment request)).sum)
    (List.attach_map_subtype_val (expand environment request task).tasks)
  apply congrArg (fun total : Nat => 1 + total)
  simpa only [agendaCost, List.map_map, Function.comp_def] using same

@[simp] theorem agendaCost_nil (cost : matcher.CursorCost) (environment : Environment) (request : Request) :
    agendaCost cost environment request [] = 0 := rfl

theorem agendaCost_cons (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (task : Task environment request matcher) (tasks : List (Task environment request matcher)) :
    agendaCost cost environment request (task :: tasks) =
      taskCost cost environment request task + agendaCost cost environment request tasks := rfl

theorem agendaCost_append (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (before after : List (Task environment request matcher)) :
    agendaCost cost environment request (before ++ after) =
      agendaCost cost environment request before + agendaCost cost environment request after := by
  simp only [agendaCost, List.map_append, List.sum_append]

theorem tick_cost (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (state : State environment request matcher) (pending : state.agenda ≠ []) :
    agendaCost cost environment request (tick environment request state).agenda + 1 =
      agendaCost cost environment request state.agenda := by
  cases agenda : state.agenda with
  | nil => exact False.elim (pending agenda)
  | cons task tasks =>
      simp only [tick, Scheduler.tick, agenda, agendaCost_append, agendaCost_cons, taskCost_eq]
      omega

theorem finiteDrain (cost : matcher.CursorCost) (environment : Environment) (request : Request)
    (state : State environment request matcher) :
    ∃ fuel : Nat, (run environment request fuel state).agenda = [] := by
  by_cases finished : state.agenda = []
  · exact ⟨0, finished⟩
  · obtain ⟨fuel, drained⟩ := finiteDrain cost environment request (tick environment request state)
    exact ⟨fuel + 1, drained⟩
termination_by agendaCost cost environment request state.agenda
decreasing_by have decreases := tick_cost cost environment request state finished; omega

#print axioms Task.rank
#print axioms phase_smaller
#print axioms count_smaller
#print axioms debt_smaller
#print axioms expandArguments_decreases
#print axioms expandMatcher_decreases
#print axioms expandDynamicInputs_decreases
#print axioms expandDynamicRows_decreases
#print axioms expand_decreases
#print axioms taskCost
#print axioms agendaCost
#print axioms taskCost_eq
#print axioms agendaCost_nil
#print axioms agendaCost_cons
#print axioms agendaCost_append
#print axioms tick_cost
#print axioms finiteDrain

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
