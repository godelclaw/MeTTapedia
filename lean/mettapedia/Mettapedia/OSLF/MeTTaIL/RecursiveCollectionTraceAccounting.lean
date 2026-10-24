import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionAccounting
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceReference

/-!
# Full receipt accounting for retained recursive matching

The account retains each captured assignment and its complete ordered
allocation history. Pending branches and already published records are
compared to the structural trace reference, not merely to a set of targets.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CollectionSelection
open CollectionMatcherCompatibility

def prefixAnswers (history : List EquationalScopedReceipts.Event) (answers : List Answer) : List Answer :=
  answers.map fun answer => ⟨answer.assignment, history ++ answer.trace⟩

@[simp] theorem prefixAnswers_nil (answers : List Answer) : prefixAnswers [] answers = answers := by
  simp [prefixAnswers]

@[simp] theorem bindAnswers_return (answers : List Answer) :
    bindAnswers answers (fun assignment => [⟨assignment, []⟩]) = answers := by
  simp [bindAnswers]

@[simp] theorem bindAnswers_empty (answers : List Answer) :
    bindAnswers answers (fun _ => []) = [] := by simp [bindAnswers]

def taskTraces (request : Request) (initial : Assignment) : Task → List Answer
  | .tree path depth schema target =>
      referenceAt request.rule request.spec request.ambient request.site path depth initial schema target
  | .arguments path depth index schemas targets =>
      referenceArguments request.rule request.spec request.ambient request.site path depth initial index schemas targets
  | .restCapture path depth name kind targets =>
      bareAnswers (captureRest? request.rule request.spec request.ambient depth request.site path
        initial name kind targets).toList
  | .bag .. | .bagSelect .. => []

def tasksTraces (request : Request) (initial : Assignment) : List Task → List Answer
  | [] => [⟨initial, []⟩]
  | task :: tasks => bindAnswers (taskTraces request initial task)
      (fun middle => tasksTraces request middle tasks)

def workTraces (request : Request) (work : Work) : List Answer :=
  prefixAnswers work.trace (tasksTraces request work.assignment work.tasks)

private theorem allocation_traces (request : Request) (path : List Nat) (depth : Nat)
    (initial : Assignment) (kind : CollType) (schemas : List Pattern) (rest : Option String)
    (allocation : Allocation Pattern) :
    ((allocationWork path depth initial kind schemas rest allocation).toList).flatMap (workTraces request) =
      prefixAnswers [⟨path, kind, allocation.decisions⟩]
        (bindAnswers (referenceArguments request.rule request.spec request.ambient request.site
          path depth initial 0 schemas allocation.values)
          (fun middle => bareAnswers (EquationalScopedMatching.finish literalBodyComparison
            request.rule request.spec request.ambient request.site path depth schemas.length
            rest kind middle (CanonicalBags.arrange kind allocation.residual)))) := by
  cases rest with
  | none =>
    by_cases empty : (CanonicalBags.arrange kind allocation.residual).isEmpty = true
    · simp [allocationWork, workTraces, tasksTraces, taskTraces,
        EquationalScopedMatching.finish, bareAnswers, empty]
    · simp [allocationWork, EquationalScopedMatching.finish, bareAnswers, empty, prefixAnswers]
  | some name =>
    simp [allocationWork, workTraces, tasksTraces, taskTraces,
      EquationalScopedMatching.finish, captureRestWith?_literal]

/-- Every local task expansion preserves complete assignment/history records. -/
theorem expand_traces (request : Request) (initial : Assignment) (task : Task) :
    (expand request initial task).flatMap (workTraces request) = taskTraces request initial task := by
  cases task with
  | tree path depth schema target =>
    cases schema <;> cases target <;>
      simp [expand, GeneralScopedMatchMachine.expand, inheritWork, workTraces,
        tasksTraces, taskTraces, referenceAt, bareAnswers, List.flatMap_map, Function.comp_def, ← List.map_eq_flatMap]
    case bvar.bvar => split <;> simp_all [tasksTraces]
    case apply.apply => split <;> simp_all [tasksTraces, taskTraces]
    case multiLambda.multiLambda => split <;> simp_all [tasksTraces, taskTraces]
    case collection.collection kind schemas rest actual targets actualRest =>
      by_cases shape : kind = actual ∧ actualRest = none
      · obtain ⟨rfl, rfl⟩ := shape
        by_cases vector : kind = .vec
        · subst kind
          cases rest <;> simp [referenceAt.eq_def, inheritWork, workTraces, tasksTraces, taskTraces]
        · simp only [true_and, vector, ↓reduceIte, referenceAt.eq_def,
            List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
          simp_rw [allocation_traces]
          rfl
      · simp [shape, referenceAt.eq_def]
  | arguments path depth index schemas targets =>
    cases schemas <;> cases targets <;>
      simp [expand, GeneralScopedMatchMachine.expand, inheritWork,
        workTraces, tasksTraces, taskTraces, referenceArguments]
  | restCapture path depth name kind targets =>
    simp [expand, GeneralScopedMatchMachine.expand, inheritWork,
      workTraces, tasksTraces, taskTraces, bareAnswers, prefixAnswers,
      List.flatMap_map, Function.comp_def, ← List.map_eq_flatMap]
  | bag => simp [expand, taskTraces]
  | bagSelect => simp [expand, taskTraces]

theorem tasksTraces_append (request : Request) (first second : List Task) (initial : Assignment) :
    tasksTraces request initial (first ++ second) =
      bindAnswers (tasksTraces request initial first) (fun middle => tasksTraces request middle second) := by
  induction first generalizing initial with
  | nil => simp [tasksTraces, bindAnswers]
  | cons task tasks ih =>
    simp only [List.cons_append, tasksTraces, ih, bindAnswers_assoc]

theorem advance_traces (request : Request) (work : Work) (pending : work.tasks ≠ []) :
    (advance request work).flatMap (workTraces request) = workTraces request work := by
  cases taskList : work.tasks with
  | nil => exact False.elim (pending taskList)
  | cons task remaining =>
    calc
      _ = prefixAnswers work.trace
          (bindAnswers ((expand request work.assignment task).flatMap (workTraces request))
            (fun middle => tasksTraces request middle remaining)) := by
        simp only [advance, taskList, List.flatMap_map, workTraces, tasksTraces_append,
          prefixAnswers, bindAnswers, List.map_flatMap, List.map_map, List.flatMap_map,
          List.flatMap_assoc, Function.comp_def, List.append_assoc]
      _ = _ := by
        rw [expand_traces]
        simp only [workTraces, taskList, tasksTraces]

def traceAccount (request : Request) (state : State) : List Answer :=
  state.answers ++ state.agenda.flatMap (workTraces request)

theorem tick_trace_account (request : Request) (state : State) :
    traceAccount request (tick request state) = traceAccount request state := by
  cases agenda : state.agenda with
  | nil => simp only [tick, agenda]
  | cons work remaining =>
    cases taskList : work.tasks with
    | nil =>
      simp [traceAccount, tick, agenda, taskList, workTraces, tasksTraces, prefixAnswers, List.append_assoc]
    | cons task tasks =>
      simp only [traceAccount, tick, agenda, taskList, List.flatMap_append, List.flatMap_cons]
      rw [advance_traces request work (by rw [taskList]; simp)]

theorem run_trace_account (request : Request) (work : Nat) (state : State) :
    traceAccount request (run request work state) = traceAccount request state := by
  induction work generalizing state with
  | zero => rfl
  | succ work ih => exact (ih (tick request state)).trans (tick_trace_account request state)

theorem start_trace_account (request : Request) :
    traceAccount request (start request) =
      referenceAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target := by
  simp [traceAccount, start, workTraces, tasksTraces, taskTraces]

theorem published_trace_prefix (request : Request) (work : Nat) :
    (run request work (start request)).answers <+:
      referenceAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target := by
  rw [← start_trace_account request, ← run_trace_account request work (start request)]
  exact List.prefix_append _ _

theorem completed_traces (request : Request) (work : Nat)
    (finished : complete (run request work (start request)) = true) :
    (run request work (start request)).answers =
      referenceAt request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target := by
  have empty := List.isEmpty_iff.mp finished
  have account := (run_trace_account request work (start request)).trans (start_trace_account request)
  simpa only [traceAccount, empty, List.flatMap_nil, List.append_nil] using account

/-- Every published nested allocation history is valid in the independently
defined receipt judgment; incomplete searches retain the same guarantee. -/
theorem published_trace_valid (request : Request) (work : Nat) {answer : Answer}
    (published : answer ∈ (run request work (start request)).answers) :
    EquationalScopedReceipts.Matches literalBodyComparison request.rule request.spec request.ambient
      request.site request.path request.depth request.initial request.schema request.target
      answer.trace answer.assignment :=
  referenceAt_sound ((published_trace_prefix request work).subset published)

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
