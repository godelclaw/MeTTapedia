import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFiniteCarrier
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCertifiedWork
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobFiniteWork
import Mettapedia.OSLF.Framework.GeneralFiniteWorkUniqueness

/-!
# Residual work of the general occurrence machine

These proof-only accounts are unique accounts of the actual pending tasks.
The ordinary executor does not compute an expansion tree before advancing a
matcher or a premise. Equation answer delivery pays for at most two new
representative visits; visitation itself is bounded by the checked carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open GeneralPremise.Scheduler

noncomputable def EquationFrame.forest (request : Request) (frame : EquationFrame request) :
    TaskForest (GeneralEquationJobExecution.expand (equationRequest request frame.source frame.job))
      frame.state.agenda :=
  Classical.choice (GeneralEquationJobExecution.reachable_finiteWork frame.reachable)

noncomputable def RuleFrame.forest (request : Request) (frame : RuleFrame request) :
    TaskForest (GeneralRuleJobExecution.expand (ruleRequest request frame.representative frame.job))
      frame.state.agenda :=
  Classical.choice (GeneralRuleJobExecution.reachable_finiteWork frame.reachable)

noncomputable def EquationFrame.debt (request : Request) (frame : EquationFrame request) : Nat :=
  (frame.forest request).cursorDebt frame.state frame.cursor 3

noncomputable def RuleFrame.debt (request : Request) (frame : RuleFrame request) : Nat :=
  (frame.forest request).cursorDebt frame.state frame.cursor 1

theorem EquationFrame.debt_positive (request : Request) (frame : EquationFrame request) :
    0 < frame.debt request := (frame.forest request).cursorDebt_positive frame.state _ _

theorem RuleFrame.debt_positive (request : Request) (frame : RuleFrame request) :
    0 < frame.debt request := (frame.forest request).cursorDebt_positive frame.state _ _

theorem EquationFrame.debt_delivered (request : Request) (frame : EquationFrame request)
    (answer : GeneralEquationJobExecution.Answer (equationRequest request frame.source frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer) :
    ({frame with cursor := frame.cursor + 1}.debt request) + 3 = frame.debt request := by
  unfold EquationFrame.debt
  rw [TaskForest.cursorDebt_unique _
    (({frame with cursor := frame.cursor + 1} : EquationFrame request).forest request)
    (frame.forest request)]
  exact (frame.forest request).cursorDebt_cursor frame.state _ _ answer found

theorem RuleFrame.debt_delivered (request : Request) (frame : RuleFrame request)
    (answer : GeneralRuleJobExecution.Answer (ruleRequest request frame.representative frame.job))
    (found : frame.state.answers[frame.cursor]? = some answer) :
    ({frame with cursor := frame.cursor + 1}.debt request) + 1 = frame.debt request := by
  unfold RuleFrame.debt
  rw [TaskForest.cursorDebt_unique _
    (({frame with cursor := frame.cursor + 1} : RuleFrame request).forest request)
    (frame.forest request)]
  exact (frame.forest request).cursorDebt_cursor frame.state _ _ answer found

theorem EquationFrame.debt_tick (request : Request) (frame : EquationFrame request)
    (pending : frame.state.agenda ≠ []) :
    (({frame with
        state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
        reachable := .tick frame.reachable} : EquationFrame request).debt request) + 1 = frame.debt request := by
  let next : EquationFrame request := {frame with
    state := GeneralEquationJobExecution.tick (equationRequest request frame.source frame.job) frame.state
    reachable := .tick frame.reachable}
  have compared := TaskForest.cursorDebt_unique next.state (next.forest request)
    ((frame.forest request).advance frame.state) frame.cursor 3
  exact (congrArg (fun debt => debt + 1) compared).trans
    ((frame.forest request).cursorDebt_tick frame.state _ _ pending)

theorem RuleFrame.debt_tick (request : Request) (frame : RuleFrame request)
    (pending : frame.state.agenda ≠ []) :
    (({frame with
        state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
        reachable := .tick frame.reachable} : RuleFrame request).debt request) + 1 = frame.debt request := by
  let next : RuleFrame request := {frame with
    state := GeneralRuleJobExecution.tick (ruleRequest request frame.representative frame.job) frame.state
    reachable := .tick frame.reachable}
  have compared := TaskForest.cursorDebt_unique next.state (next.forest request)
    ((frame.forest request).advance frame.state) frame.cursor 1
  exact (congrArg (fun debt => debt + 1) compared).trans
    ((frame.forest request).cursorDebt_tick frame.state _ _ pending)

noncomputable def equationBatchDebt (request : Request) (source : Syntax.Pattern) : Nat :=
  ((equationTasks request source).map fun task => match task with
    | .equation frame => frame.debt request
    | _ => 0).sum

noncomputable def universeDebt (request : Request) (patterns : List Syntax.Pattern) : Nat :=
  (patterns.map (equationBatchDebt request)).sum + patterns.length + 1

noncomputable def taskDebt (request : Request) : Task request → Nat
  | .visit _ => 1
  | .incoming _ edges => 2 * edges.length + 1
  | .universe => universeDebt request request.universe + 1
  | .scanUniverse remaining => universeDebt request remaining
  | .equation frame => frame.debt request
  | .rule frame => frame.debt request

noncomputable def tasksDebt (request : Request) (tasks : List (Task request)) : Nat :=
  (tasks.map (taskDebt request)).sum

theorem tasksDebt_nil (request : Request) : tasksDebt request [] = 0 := rfl

theorem tasksDebt_cons (request : Request) (task : Task request) (tasks : List (Task request)) :
    tasksDebt request (task :: tasks) = taskDebt request task + tasksDebt request tasks := by
  simp only [tasksDebt, List.map_cons, List.sum_cons]

theorem tasksDebt_append (request : Request) (first second : List (Task request)) :
    tasksDebt request (first ++ second) = tasksDebt request first + tasksDebt request second := by
  simp only [tasksDebt, List.map_append, List.sum_append]

theorem taskDebt_positive (request : Request) (task : Task request) : 0 < taskDebt request task := by
  cases task with
  | equation frame => exact frame.debt_positive request
  | rule frame => exact frame.debt_positive request
  | visit _ => change 0 < 1; decide
  | incoming _ _ => simp only [taskDebt]; omega
  | «universe» => simp only [taskDebt, universeDebt]; omega
  | scanUniverse _ => simp only [taskDebt, universeDebt]; omega

theorem equationBatchDebt_eq (request : Request) (source : Syntax.Pattern) :
    equationBatchDebt request source = tasksDebt request (equationTasks request source) := by
  unfold equationBatchDebt tasksDebt
  apply congrArg List.sum
  apply List.map_congr_left
  intro task member
  simp only [equationTasks, List.mem_map, List.mem_attach, true_and] at member
  obtain ⟨item, same⟩ := member
  subst task
  rfl

theorem universeDebt_cons (request : Request) (source : Syntax.Pattern) (remaining : List Syntax.Pattern) :
    universeDebt request (source :: remaining) =
      tasksDebt request (equationTasks request source) + universeDebt request remaining + 1 := by
  simp only [universeDebt, List.map_cons, List.sum_cons, List.length_cons, equationBatchDebt_eq]
  omega

theorem edgeDiscoveries_debt (request : Request) (state : State request) (edge : Edge request) :
    tasksDebt request (edgeDiscoveries request state edge) ≤ 2 := by
  unfold edgeDiscoveries
  rw [tasksDebt_append]
  cases visitedAt request state edge.source <;>
    cases visitedAt request state edge.receipt.target <;>
    simp only [tasksDebt_cons, tasksDebt_nil, taskDebt] <;> omega

theorem expandRule_debt (request : Request) (frame : RuleFrame request) :
    tasksDebt request (expandRule request frame).tasks < frame.debt request := by
  unfold expandRule
  split
  · split
    · simp only [tasksDebt_nil]; exact frame.debt_positive request
    · rename_i pending
      have nonempty : frame.state.agenda ≠ [] := by
        intro empty
        apply pending
        change frame.state.agenda.isEmpty = true
        exact List.isEmpty_iff.mpr empty
      have decreased := frame.debt_tick request nonempty
      simp only [tasksDebt_cons, tasksDebt_nil, taskDebt]
      omega
  · rename_i answer found
    have decreased := frame.debt_delivered request answer found
    simp only [tasksDebt_cons, tasksDebt_nil, taskDebt]
    omega

theorem expandEquation_debt (request : Request) (state : State request) (frame : EquationFrame request) :
    tasksDebt request (expandEquation request state frame).tasks < frame.debt request := by
  unfold expandEquation
  split
  · split
    · simp only [tasksDebt_nil]; exact frame.debt_positive request
    · rename_i pending
      have nonempty : frame.state.agenda ≠ [] := by
        intro empty
        apply pending
        change frame.state.agenda.isEmpty = true
        exact List.isEmpty_iff.mpr empty
      have decreased := frame.debt_tick request nonempty
      simp only [tasksDebt_cons, tasksDebt_nil, taskDebt]
      omega
  · rename_i answer found
    have decreased := frame.debt_delivered request answer found
    have added := edgeDiscoveries_debt request state ⟨frame.source, answer.val, answer.property⟩
    simp only [tasksDebt_append, tasksDebt_cons, tasksDebt_nil, taskDebt]
    omega

theorem expand_debt_without_visit (request : Request) (state : State request) (task : Task request)
    (unchanged : (expand request state task).visits = []) :
    tasksDebt request (expand request state task).tasks < taskDebt request task := by
  cases task with
  | equation frame => exact expandEquation_debt request state frame
  | rule frame => exact expandRule_debt request frame
  | visit representative =>
      simp only [expand] at unchanged ⊢
      split
      · simp only [tasksDebt_nil, taskDebt]; omega
      · rename_i unseen
        simp only [if_neg unseen] at unchanged
        exact False.elim (List.cons_ne_nil _ _ unchanged)
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, tasksDebt_nil, taskDebt, List.length_nil]; decide
      | cons edge remaining =>
          simp only [expand]
          repeat' split
          all_goals simp only [tasksDebt_cons, tasksDebt_nil, taskDebt, List.length_cons]
          all_goals omega
  | «universe» =>
      simp only [expand, tasksDebt_cons, tasksDebt_nil, taskDebt]
      omega
  | scanUniverse remaining =>
      cases remaining with
      | nil => simp only [expand, tasksDebt_nil, taskDebt, universeDebt, List.map_nil,
          List.sum_nil, List.length_nil]; decide
      | cons source remaining =>
          simp only [expand, tasksDebt_append, tasksDebt_cons, tasksDebt_nil, taskDebt,
            universeDebt_cons]
          omega

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
