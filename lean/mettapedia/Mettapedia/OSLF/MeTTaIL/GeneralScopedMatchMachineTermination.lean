import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-!
# Structural termination of suspended matcher work

The first measure counts unfinished schema operations. A bag cursor may keep
this measure while consuming one actual residual position; the second measure
counts those positions. Each successor branch is therefore strictly smaller,
including the continuation that resumes the next bag alternative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

mutual
def schemaWeight : Pattern → Nat
  | .bvar _ | .fvar _ => 1
  | .apply _ arguments => argumentWeight arguments + 2
  | .lambda _ body | .multiLambda _ _ body => schemaWeight body + 1
  | .subst body replacement => schemaWeight body + schemaWeight replacement + 1
  | .collection _ elements _ => argumentWeight elements + 4
termination_by schema => sizeOf schema

def argumentWeight : List Pattern → Nat
  | [] => 0
  | schema :: schemas => schemaWeight schema + argumentWeight schemas + 1
termination_by schemas => sizeOf schemas
end

def Task.primary : Task → Nat
  | .tree _ _ schema _ => schemaWeight schema
  | .arguments _ _ _ schemas _ => argumentWeight schemas + 1
  | .bag _ _ _ schemas _ _ _ => argumentWeight schemas + 3
  | .bagSelect _ _ _ schema schemas _ _ _ _ => argumentWeight (schema :: schemas) + 2
  | .restCapture _ _ _ _ _ => 1

def Task.secondary : Task → Nat
  | .bagSelect _ _ _ _ _ _ _ targets selected => targets.length - selected
  | _ => 0

def tasksPrimary : List Task → Nat
  | [] => 0
  | task :: tasks => task.primary + tasksPrimary tasks

def tasksSecondary : List Task → Nat
  | [] => 0
  | task :: tasks => task.secondary + tasksSecondary tasks

def Smaller (left right : Work) : Prop :=
  tasksPrimary left.tasks < tasksPrimary right.tasks ∨
    tasksPrimary left.tasks = tasksPrimary right.tasks ∧
      tasksSecondary left.tasks < tasksSecondary right.tasks

theorem expand_decreases (request : Request) (initial : Assignment) (task : Task)
    (branch : Work) (member : branch ∈ expand request initial task) :
    tasksPrimary branch.tasks < task.primary ∨
      tasksPrimary branch.tasks = task.primary ∧ tasksSecondary branch.tasks < task.secondary := by
  cases task with
  | tree path depth schema target =>
    cases schema with
    | fvar name =>
      obtain ⟨final, _, same⟩ := List.mem_map.mp member
      subst branch
      exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
    | bvar expected =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      · simp only [List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
      · contradiction
    | apply label schemas =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      · simp only [List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
      · contradiction
    | lambda display body =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      simp only [List.mem_singleton] at member
      subst branch
      exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
    | multiLambda arity display body =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      · simp only [List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
      · contradiction
    | subst body replacement =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      simp only [List.mem_singleton] at member
      subst branch
      exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
    | collection kind schemas rest =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      · split at member
        · cases rest with
          | none =>
            simp only [List.mem_singleton] at member
            subst branch
            exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
          | some name =>
            simp only [List.mem_singleton] at member
            subst branch
            exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
        · simp only [List.mem_singleton] at member
          subst branch
          exact .inl (by simp only [tasksPrimary, Task.primary, schemaWeight]; omega)
      · contradiction
  | arguments path depth index schemas targets =>
    cases schemas with
    | nil =>
      cases targets <;> simp only [expand] at member
      · simp only [List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, argumentWeight]; omega)
      · contradiction
    | cons schema schemas =>
      cases targets <;> simp only [expand] at member
      · contradiction
      · simp only [List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, argumentWeight]; omega)
  | bag path depth index schemas rest kind targets =>
    cases schemas with
    | nil =>
      cases rest with
      | none =>
        simp only [expand] at member
        split at member
        · simp only [List.mem_singleton] at member
          subst branch
          exact .inl (by simp only [tasksPrimary, Task.primary, argumentWeight]; omega)
        · contradiction
      | some name =>
        simp only [expand, List.mem_singleton] at member
        subst branch
        exact .inl (by simp only [tasksPrimary, Task.primary, argumentWeight]; omega)
    | cons schema schemas =>
      simp only [expand, List.mem_singleton] at member
      subst branch
      exact .inl (by simp only [tasksPrimary, Task.primary]; omega)
  | bagSelect path depth index schema schemas rest kind targets selected =>
    cases found : targets[selected]? with
    | none => simp only [expand, found, List.not_mem_nil] at member
    | some target =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      simp only [expand, found, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst branch
      · exact .inr ⟨by simp only [tasksPrimary, Task.primary, argumentWeight]; omega,
          by simp only [tasksSecondary, Task.secondary]; omega⟩
      · exact .inr ⟨by simp only [tasksPrimary, Task.primary],
          by simp only [tasksSecondary, Task.secondary]; omega⟩
  | restCapture path depth name kind targets =>
    obtain ⟨final, _, same⟩ := List.mem_map.mp member
    subst branch
    exact .inl (by simp only [tasksPrimary, Task.primary]; omega)

theorem tasksPrimary_append (before after : List Task) :
    tasksPrimary (before ++ after) = tasksPrimary before + tasksPrimary after := by
  induction before with
  | nil => simp [tasksPrimary]
  | cons task tasks ih => simp only [List.cons_append, tasksPrimary, ih, Nat.add_assoc]

theorem tasksSecondary_append (before after : List Task) :
    tasksSecondary (before ++ after) = tasksSecondary before + tasksSecondary after := by
  induction before with
  | nil => simp [tasksSecondary]
  | cons task tasks ih => simp only [List.cons_append, tasksSecondary, ih, Nat.add_assoc]

theorem advance_decreases (request : Request) (work branch : Work)
    (member : branch ∈ advance request work) : Smaller branch work := by
  cases tasks : work.tasks with
  | nil => simp only [advance, tasks, List.not_mem_nil] at member
  | cons task tasks =>
    simp only [advance, tasks, List.mem_map] at member
    obtain ⟨expanded, generated, same⟩ := member
    subst branch
    have decreases := expand_decreases request work.assignment task expanded generated
    simp only [Smaller, tasksPrimary_append, tasksSecondary_append, tasksPrimary, tasksSecondary, tasks]
    rcases decreases with strict | ⟨same, strict⟩
    · exact .inl (by omega)
    · exact .inr ⟨by omega, by omega⟩

/-- This finite expansion cost is derived from structural decrease. It is
used only to establish eventual drain; start and tick do not compute it. -/
def workCost (request : Request) (work : Work) : Nat :=
  1 + ((advance request work).attach.map fun branch => workCost request branch.val).sum
termination_by (tasksPrimary work.tasks, tasksSecondary work.tasks)
decreasing_by
  have smaller := advance_decreases request work branch.val branch.property
  rcases smaller with smaller | ⟨same, smaller⟩
  · exact Prod.Lex.left _ _ smaller
  · rw [same]
    exact Prod.Lex.right _ smaller

def agendaCost (request : Request) (agenda : List Work) : Nat :=
  (agenda.map (workCost request)).sum

theorem workCost_eq (request : Request) (work : Work) :
    workCost request work = 1 + agendaCost request (advance request work) := by
  rw [workCost.eq_def]
  have same := congrArg (fun agenda : List Work => (agenda.map (workCost request)).sum)
    (List.attach_map_subtype_val (advance request work))
  simp only [agendaCost]
  apply congrArg (fun total : Nat => 1 + total)
  simpa only [List.map_map, Function.comp_def] using same

theorem agendaCost_nil (request : Request) : agendaCost request [] = 0 := rfl

theorem agendaCost_cons (request : Request) (work : Work) (agenda : List Work) :
    agendaCost request (work :: agenda) = workCost request work + agendaCost request agenda := rfl

theorem agendaCost_append (request : Request) (before after : List Work) :
    agendaCost request (before ++ after) = agendaCost request before + agendaCost request after := by
  simp only [agendaCost, List.map_append, List.sum_append]

theorem tick_cost {request : Request} {state : State} (pending : complete state = false) :
    agendaCost request (tick request state).agenda < agendaCost request state.agenda := by
  cases agenda : state.agenda with
  | nil => simp only [complete, agenda, List.isEmpty_nil, Bool.true_eq_false] at pending
  | cons work rest =>
    cases tasks : work.tasks with
    | nil =>
      have cost : workCost request work = 1 := by
        rw [workCost_eq]
        simp only [advance, tasks, agendaCost_nil, Nat.add_zero]
      simp only [tick, agenda, tasks, agendaCost_cons, cost]
      omega
    | cons task tasks =>
      simp only [tick, agenda, tasks, agendaCost_append, agendaCost_cons, workCost_eq]
      omega

theorem finiteDrain (request : Request) (state : State) :
    ∃ fuel : Nat, complete (run request fuel state) = true := by
  by_cases finished : complete state = true
  · exact ⟨0, finished⟩
  · have pending : complete state = false := Bool.eq_false_iff.mpr finished
    obtain ⟨fuel, drained⟩ := finiteDrain request (tick request state)
    exact ⟨fuel + 1, drained⟩
termination_by agendaCost request state.agenda
decreasing_by exact tick_cost pending

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
