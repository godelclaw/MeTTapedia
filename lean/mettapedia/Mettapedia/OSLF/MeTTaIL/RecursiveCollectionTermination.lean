import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

/-!
# Finite drain of retained recursive collection matching

The established scoped schema measure decreases for each expansion branch.
Collection allocations change the number of branches, but each branch consumes
its collection node. The derived finite-tree cost proves eventual exhaustion;
the executable machine does not compute that cost when it runs or resumes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax ScopedRuleMatching CollectionSelection
open GeneralScopedMatchMachine (tasksPrimary tasksSecondary schemaWeight argumentWeight)

private theorem inherited_decreases (request : Request) (initial : Assignment)
    (task : Task) {branch : Work}
    (member : branch ∈ (GeneralScopedMatchMachine.expand request initial task).map inheritWork) :
    tasksPrimary branch.tasks < task.primary ∨
      tasksPrimary branch.tasks = task.primary ∧ tasksSecondary branch.tasks < task.secondary := by
  obtain ⟨original, generated, rfl⟩ := List.mem_map.mp member
  exact GeneralScopedMatchMachine.expand_decreases request initial task original generated

theorem expand_decreases (request : Request) (initial : Assignment) (task : Task)
    {branch : Work} (member : branch ∈ expand request initial task) :
    tasksPrimary branch.tasks < task.primary ∨
      tasksPrimary branch.tasks = task.primary ∧ tasksSecondary branch.tasks < task.secondary := by
  unfold expand at member
  split at member
  next path depth kind schemas rest actual targets actualRest =>
    split at member
    · split at member
      · exact inherited_decreases request initial _ member
      · obtain ⟨allocation, _, accepted⟩ := List.mem_filterMap.mp member
        cases rest with
        | none =>
          simp only [allocationWork] at accepted
          split at accepted
          · cases accepted
            exact .inl (by simp only [tasksPrimary, GeneralScopedMatchMachine.Task.primary, schemaWeight]; omega)
          · cases accepted
        | some name =>
          simp only [allocationWork, Option.some.injEq] at accepted
          subst branch
          exact .inl (by simp only [tasksPrimary, GeneralScopedMatchMachine.Task.primary, schemaWeight]; omega)
    · cases member
  next => exact inherited_decreases request initial _ member
  next => exact inherited_decreases request initial _ member
  next => exact inherited_decreases request initial _ member
  next => cases member
  next => cases member

def Smaller (left right : Work) : Prop :=
  tasksPrimary left.tasks < tasksPrimary right.tasks ∨
    tasksPrimary left.tasks = tasksPrimary right.tasks ∧
      tasksSecondary left.tasks < tasksSecondary right.tasks

theorem advance_decreases (request : Request) (work branch : Work)
    (member : branch ∈ advance request work) : Smaller branch work := by
  cases tasks : work.tasks with
  | nil => simp only [advance, tasks, List.not_mem_nil] at member
  | cons task tasks =>
    simp only [advance, tasks] at member
    obtain ⟨expanded, generated, rfl⟩ := List.mem_map.mp member
    have smaller := expand_decreases request work.assignment task generated
    simp only [Smaller, GeneralScopedMatchMachine.tasksPrimary_append,
      GeneralScopedMatchMachine.tasksSecondary_append, tasksPrimary, tasksSecondary, tasks]
    rcases smaller with strict | ⟨same, strict⟩
    · exact .inl (by omega)
    · exact .inr ⟨by omega, by omega⟩

/-- A proof-side finite expansion tree; neither start nor tick evaluates it. -/
def workCost (request : Request) (work : Work) : Nat :=
  1 + ((advance request work).attach.map fun branch => workCost request branch.val).sum
termination_by (tasksPrimary work.tasks, tasksSecondary work.tasks)
decreasing_by
  have smaller := advance_decreases request work branch.val branch.property
  rcases smaller with strict | ⟨same, strict⟩
  · exact Prod.Lex.left _ _ strict
  · rw [same]
    exact Prod.Lex.right _ strict

def agendaCost (request : Request) (agenda : List Work) : Nat :=
  (agenda.map (workCost request)).sum

theorem workCost_eq (request : Request) (work : Work) :
    workCost request work = 1 + agendaCost request (advance request work) := by
  rw [workCost.eq_def]
  have same := congrArg (fun agenda : List Work => (agenda.map (workCost request)).sum)
    (List.attach_map_subtype_val (advance request work))
  apply congrArg (fun total : Nat => 1 + total)
  simpa only [agendaCost, List.map_map, Function.comp_def] using same

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
        simp [advance, tasks, agendaCost]
      simp only [tick, agenda, tasks, agendaCost, List.map_cons, List.sum_cons, cost]
      omega
    | cons task tasks =>
      simp only [tick, agenda, tasks]
      change agendaCost request (advance request work ++ rest) <
        workCost request work + agendaCost request rest
      rw [agendaCost_append, workCost_eq]
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

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
