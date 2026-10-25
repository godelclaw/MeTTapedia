import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQuery
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination

/-!
# Structural drainage of interrupted finite queries

Provider rows and query arguments are finite. Matcher continuations use the
earned structural expansion cost, together with the number of answers still
to be consumed. This measure concerns retained work rather than a supplied
query oracle or a guessed fuel cutoff.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching

abbrev Rank := Nat × (Nat × Nat)

def Task.rank (environment : Environment) (request : Request) :
    Task environment request → Rank
  | .start => (5, 0, 0)
  | .rows frame => (3, environment.provider.rows.length - frame.cursor, 0)
  | .dynamicInputs frame => (4, frame.schemas.length, 0)
  | .dynamicRows frame => (3, frame.rows.length - frame.cursor, 0)
  | .arguments frame => (2, 2 * frame.schemas.length + 1, 0)
  | .matcher frame => (2, 2 * frame.schemas.length + 2,
      2 * GeneralScopedMatchMachine.agendaCost frame.query frame.state.agenda +
        (frame.state.answers.length - frame.cursor) + 1)

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

theorem expandArguments_decreases (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request) (branch : Task environment request)
    (member : branch ∈ (expandArguments environment request frame).tasks) :
    RankSmaller (branch.rank environment request)
      ((Task.arguments frame).rank environment request) := by
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

theorem expandMatcher_decreases (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request) (branch : Task environment request)
    (member : branch ∈ (expandMatcher environment request frame).tasks) :
    RankSmaller (branch.rank environment request)
      ((Task.matcher frame).rank environment request) := by
  unfold expandMatcher at member
  split at member
  · rename_i answer found
    change frame.state.answers[frame.cursor]? = some answer at found
    have within := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst branch
    · apply count_smaller
      dsimp only
      omega
    · apply debt_smaller
      dsimp only
      omega
  · rename_i found
    split at member
    · simp at member
    · rename_i pending
      have pending' : GeneralScopedMatchMachine.complete frame.state = false :=
        Bool.eq_false_iff.mpr pending
      have decreases := GeneralScopedMatchMachine.tick_cost (request := frame.query) pending'
      have emitted := GeneralScopedMatchMachine.tick_answers_length frame.query frame.state
      have consumed : frame.state.answers.length ≤ frame.cursor :=
        List.getElem?_eq_none_iff.mp found
      simp only [List.mem_singleton] at member
      subst branch
      apply debt_smaller
      dsimp only
      omega

theorem expandDynamicInputs_decreases (environment : Environment) (request : Request)
    (frame : DynamicInputsFrame environment request) (branch : Task environment request)
    (member : branch ∈ (expandDynamicInputs environment request frame).tasks) :
    RankSmaller (branch.rank environment request) ((Task.dynamicInputs frame).rank environment request) := by
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

theorem expandDynamicRows_decreases (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (branch : Task environment request)
    (member : branch ∈ (expandDynamicRows environment request frame).tasks) :
    RankSmaller (branch.rank environment request) ((Task.dynamicRows frame).rank environment request) := by
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

theorem expand_decreases (environment : Environment) (request : Request)
    (task branch : Task environment request)
    (member : branch ∈ (expand environment request task).tasks) :
    RankSmaller (branch.rank environment request) (task.rank environment request) := by
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
  | dynamicInputs frame => exact expandDynamicInputs_decreases _ _ _ _ member
  | dynamicRows frame => exact expandDynamicRows_decreases _ _ _ _ member
  | arguments frame => exact expandArguments_decreases _ _ _ _ member
  | matcher frame => exact expandMatcher_decreases _ _ _ _ member

def taskCost (environment : Environment) (request : Request)
    (task : Task environment request) : Nat :=
  1 + (((expand environment request task).tasks.attach.map fun branch =>
    taskCost environment request branch.val).sum)
termination_by task.rank environment request
decreasing_by exact expand_decreases environment request task branch.val branch.property

def agendaCost (environment : Environment) (request : Request)
    (agenda : List (Task environment request)) : Nat :=
  (agenda.map (taskCost environment request)).sum

theorem taskCost_eq (environment : Environment) (request : Request)
    (task : Task environment request) :
    taskCost environment request task =
      1 + agendaCost environment request (expand environment request task).tasks := by
  rw [taskCost.eq_def]
  have same := congrArg (fun agenda : List (Task environment request) =>
      (agenda.map (taskCost environment request)).sum)
    (List.attach_map_subtype_val (expand environment request task).tasks)
  apply congrArg (fun total : Nat => 1 + total)
  simpa only [agendaCost, List.map_map, Function.comp_def] using same

@[simp] theorem agendaCost_nil (environment : Environment) (request : Request) :
    agendaCost environment request [] = 0 := rfl

theorem agendaCost_cons (environment : Environment) (request : Request)
    (task : Task environment request) (tasks : List (Task environment request)) :
    agendaCost environment request (task :: tasks) =
      taskCost environment request task + agendaCost environment request tasks := rfl

theorem agendaCost_append (environment : Environment) (request : Request)
    (before after : List (Task environment request)) :
    agendaCost environment request (before ++ after) =
      agendaCost environment request before + agendaCost environment request after := by
  simp only [agendaCost, List.map_append, List.sum_append]

theorem tick_cost (environment : Environment) (request : Request)
    (state : State environment request) (pending : state.agenda ≠ []) :
    agendaCost environment request (tick environment request state).agenda + 1 =
      agendaCost environment request state.agenda := by
  cases agenda : state.agenda with
  | nil => exact False.elim (pending agenda)
  | cons task tasks =>
      simp only [tick, Scheduler.tick, agenda, agendaCost_append, agendaCost_cons, taskCost_eq]
      omega

theorem finiteDrain (environment : Environment) (request : Request)
    (state : State environment request) :
    ∃ fuel : Nat, (run environment request fuel state).agenda = [] := by
  by_cases finished : state.agenda = []
  · exact ⟨0, finished⟩
  · obtain ⟨fuel, drained⟩ := finiteDrain environment request (tick environment request state)
    exact ⟨fuel + 1, drained⟩
termination_by agendaCost environment request state.agenda
decreasing_by have decreases := tick_cost environment request state finished; omega

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
