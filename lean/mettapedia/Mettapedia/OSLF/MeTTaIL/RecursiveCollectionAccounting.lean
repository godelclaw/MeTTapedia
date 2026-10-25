import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTermination
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingNormalization

/-!
# Assignment accounting for suspended recursive matching

The reference is the independently specified recursive collection matcher.
Pending tasks denote its remaining assignment lists. Publication and the
pending agenda must jointly retain that list, including repeated assignments
from distinct allocations. Allocation-event validity is a further trace-level
obligation; this readout does not identify logical derivations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CollectionSelection
open CollectionMatcherCompatibility

def taskAssignments (request : Request) (initial : Assignment) : Task → List Assignment
  | .tree path depth schema target =>
      EquationalScopedMatching.runAt literalBodyComparison request.rule request.spec
        request.ambient request.site path depth initial schema target
  | .arguments path depth index schemas targets =>
      EquationalScopedMatching.runArguments literalBodyComparison request.rule request.spec
        request.ambient request.site path depth initial index schemas targets
  | .restCapture path depth name kind targets =>
      (captureRest? request.rule request.spec request.ambient depth request.site path
        initial name kind targets).toList
  | .bag .. | .bagSelect .. => []

def tasksAssignments (request : Request) (initial : Assignment) : List Task → List Assignment
  | [] => [initial]
  | task :: tasks => (taskAssignments request initial task).flatMap
      fun middle => tasksAssignments request middle tasks

def workAssignments (request : Request) (work : Work) : List Assignment :=
  tasksAssignments request work.assignment work.tasks

private theorem allocation_assignments (request : Request) (path : List Nat) (depth : Nat)
    (initial : Assignment) (kind : CollType) (schemas : List Pattern) (rest : Option String)
    (allocation : Allocation Pattern) :
    ((allocationWork path depth initial kind schemas rest allocation).toList).flatMap
      (workAssignments request) =
      (EquationalScopedMatching.runArguments literalBodyComparison request.rule request.spec
        request.ambient request.site path depth initial 0 schemas allocation.values).flatMap
        (fun middle => EquationalScopedMatching.finish literalBodyComparison request.rule request.spec
          request.ambient request.site path depth schemas.length rest kind middle
          (CanonicalBags.arrange kind allocation.residual)) := by
  cases rest with
  | none =>
    by_cases empty : (CanonicalBags.arrange kind allocation.residual).isEmpty = true
    · simp [allocationWork, workAssignments, tasksAssignments, taskAssignments,
        EquationalScopedMatching.finish, empty]
    · simp [allocationWork, EquationalScopedMatching.finish, empty]
  | some name =>
    simp [allocationWork, workAssignments, tasksAssignments, taskAssignments,
      EquationalScopedMatching.finish, captureRestWith?_literal]

/-- One actual task expansion retains exactly the reference answer list. -/
theorem expand_assignments (request : Request) (initial : Assignment) (task : Task) :
    (expand request initial task).flatMap (workAssignments request) =
      taskAssignments request initial task := by
  cases task with
  | tree path depth schema target =>
    cases schema <;> cases target <;>
      simp [expand, GeneralScopedMatchMachine.expand, inheritWork,
        workAssignments, tasksAssignments, taskAssignments,
        EquationalScopedMatching.runAt, captureWith?_literal,
        List.flatMap_map, Function.comp_def]
    case bvar.bvar => split <;> simp_all [tasksAssignments]
    case apply.apply => split <;> simp_all [tasksAssignments, taskAssignments]
    case multiLambda.multiLambda => split <;> simp_all [tasksAssignments, taskAssignments]
    case collection.collection kind schemas rest actual targets actualRest =>
      by_cases shape : kind = actual ∧ actualRest = none
      · obtain ⟨rfl, rfl⟩ := shape
        by_cases vector : kind = .vec
        · subst kind
          cases rest <;>
            simp [EquationalScopedMatching.runAt.eq_def, inheritWork, workAssignments,
              tasksAssignments, taskAssignments, captureRestWith?_literal, List.filterMap_eq_flatMap_toList]
        · simp only [true_and, vector, ↓reduceIte,
            EquationalScopedMatching.runAt.eq_def, List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
          simp_rw [allocation_assignments]
          rw [kindAllocations, ← tracedAllocations_erase]
          simp only [List.flatMap_map, Allocation.erase]
      · simp [shape, EquationalScopedMatching.runAt.eq_def]

  | arguments path depth index schemas targets =>
    cases schemas <;> cases targets <;>
      simp [expand, GeneralScopedMatchMachine.expand, inheritWork,
        workAssignments, tasksAssignments, taskAssignments,
        EquationalScopedMatching.runArguments]
  | restCapture path depth name kind targets =>
    simp [expand, GeneralScopedMatchMachine.expand, inheritWork,
      workAssignments, tasksAssignments, taskAssignments, List.flatMap_map, Function.comp_def]
  | bag => simp [expand, taskAssignments]
  | bagSelect => simp [expand, taskAssignments]

theorem tasksAssignments_append (request : Request) (first second : List Task)
    (initial : Assignment) :
    tasksAssignments request initial (first ++ second) =
      (tasksAssignments request initial first).flatMap
        (fun middle => tasksAssignments request middle second) := by
  induction first generalizing initial with
  | nil => simp [tasksAssignments]
  | cons task tasks ih =>
    simp only [List.cons_append, tasksAssignments, ih, List.flatMap_assoc]

theorem advance_assignments (request : Request) (work : Work)
    (pending : work.tasks ≠ []) :
    (advance request work).flatMap (workAssignments request) = workAssignments request work := by
  cases tasks : work.tasks with
  | nil => exact False.elim (pending tasks)
  | cons task remaining =>
    calc
      _ = ((expand request work.assignment task).flatMap (workAssignments request)).flatMap
          (fun middle => tasksAssignments request middle remaining) := by
        simp only [advance, tasks, List.flatMap_map, workAssignments,
          tasksAssignments_append, List.flatMap_assoc]
      _ = _ := by
        rw [expand_assignments]
        simp only [workAssignments, tasksAssignments, tasks]

def assignmentAccount (request : Request) (state : State) : List Assignment :=
  state.answers.map (·.assignment) ++ state.agenda.flatMap (workAssignments request)

/-- Publication and pending work jointly retain the exact ordered answer list.
Suspending a branch does not erase its allocation's future answers. -/
theorem tick_assignment_account (request : Request) (state : State) :
    assignmentAccount request (tick request state) = assignmentAccount request state := by
  cases agenda : state.agenda with
  | nil => simp only [tick, agenda]
  | cons work rest =>
    cases tasks : work.tasks with
    | nil =>
      simp only [assignmentAccount, tick, agenda, tasks, List.map_append, List.map_cons,
        List.map_nil, List.flatMap_cons, workAssignments, tasksAssignments,
        List.append_assoc, List.singleton_append]
    | cons task tasks =>
      simp only [assignmentAccount, tick, agenda, tasks, List.flatMap_append, List.flatMap_cons]
      rw [advance_assignments request work (by rw [tasks]; simp)]

theorem run_assignment_account (request : Request) (work : Nat) (state : State) :
    assignmentAccount request (run request work state) = assignmentAccount request state := by
  induction work generalizing state with
  | zero => rfl
  | succ work ih => exact (ih (tick request state)).trans (tick_assignment_account request state)

theorem start_assignment_account (request : Request) :
    assignmentAccount request (start request) =
      EquationalScopedMatching.runAt literalBodyComparison request.rule request.spec request.ambient
        request.site request.path request.depth request.initial request.schema request.target := by
  simp [assignmentAccount, start, workAssignments, tasksAssignments, taskAssignments]

/-- Every interrupted publication is a prefix of the independently computed
recursive answer list, including repeated assignments. -/
theorem published_assignment_prefix (request : Request) (work : Nat) :
    ((run request work (start request)).answers.map (·.assignment)) <+:
      EquationalScopedMatching.runAt literalBodyComparison request.rule request.spec request.ambient
        request.site request.path request.depth request.initial request.schema request.target := by
  rw [← start_assignment_account request, ← run_assignment_account request work (start request)]
  exact List.prefix_append _ _

theorem completed_assignments (request : Request) (work : Nat)
    (finished : complete (run request work (start request)) = true) :
    ((run request work (start request)).answers.map (·.assignment)) =
      EquationalScopedMatching.runAt literalBodyComparison request.rule request.spec request.ambient
        request.site request.path request.depth request.initial request.schema request.target := by
  have empty := List.isEmpty_iff.mp finished
  have account := (run_assignment_account request work (start request)).trans (start_assignment_account request)
  simpa only [assignmentAccount, empty, List.flatMap_nil, List.append_nil] using account

theorem eventually_exact_assignments (request : Request) :
    ∃ work, complete (run request work (start request)) = true ∧
      ((run request work (start request)).answers.map (·.assignment)) =
        EquationalScopedMatching.runAt literalBodyComparison request.rule request.spec request.ambient
          request.site request.path request.depth request.initial request.schema request.target := by
  obtain ⟨work, finished⟩ := finiteDrain request (start request)
  exact ⟨work, finished, completed_assignments request work finished⟩

/-- Every already published capture has an ordinary scoped source witness
at an equivalent presentation. No complete-search hypothesis is needed. -/
theorem published_ordinary_source (request : Request) (work : Nat) {answer : Answer}
    (published : answer ∈ (run request work (start request)).answers) :
    ∃ presented trace, CanonicalBags.Same request.target presented ∧
      GeneralScopedMatchMachine.TracedMatches request.rule request.spec request.ambient
        request.site request.path request.depth request.initial request.schema presented
        trace answer.assignment := by
  have member := (published_assignment_prefix request work).subset
    (List.mem_map_of_mem (f := Answer.assignment) published)
  exact EquationalScopedMatching.runAt_has_ordinary_presentation member

/-- Completed retained execution covers ordinary matching from every source
presentation, after canonicalizing the source and its captured assignment. -/
theorem completed_covers_presentation (request : Request) (work : Nat)
    (finished : complete (run request work (start request)) = true)
    (increasing : CanonicalBags.IncreasingSpines request.rule request.spec)
    {initial captured : Assignment} {source presented : Pattern}
    (target : request.target = CanonicalBags.canon source)
    (initialEq : request.initial = CanonicalBags.canonAssignment initial)
    (same : CanonicalBags.Same source presented)
    (matched : GeneralScopedMatch.Matches request.rule request.spec request.ambient
      request.site request.path request.depth initial request.schema presented captured) :
    ∃ answer ∈ (run request work (start request)).answers,
      answer.assignment = CanonicalBags.canonAssignment captured := by
  apply List.mem_map.mp
  rw [completed_assignments request work finished, target, initialEq]
  exact EquationalScopedMatching.runAt_covers_presentation increasing same matched

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
