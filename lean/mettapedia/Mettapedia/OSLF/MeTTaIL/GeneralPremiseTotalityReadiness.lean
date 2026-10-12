import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout

/-!
# Checked readiness of complete continuation work

Primitive readiness checks inspect signatures, occurrence projections, finite
collection representations and typed local bindings. They are distinct from
semantic success: a false query or freshness test is a resolved outcome.
The finite work tree checks every branch, including branches without answers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace Query

def checkTaskReady (environment : Environment) (request : Request) :
    Task environment request → Bool
  | .start => (signature? environment.provider request.relation request.arguments.length).isSome
  | .rows _ => true
  | .arguments frame =>
      match frame.schemas, frame.values, frame.modes with
      | [], [], [] => true
      | schema :: _, _ :: _, .input :: _ =>
          (instantiateAt? request.context.rule request.context.spec request.context.bound.length
            (request.context.site frame.index) [] 0 frame.assignment schema).isSome
      | _ :: _, _ :: _, .output :: _ => true
      | _, _, _ => false
  | .matcher _ => true

theorem checkTaskReady_sound (environment : Environment) (request : Request)
    (task : Task environment request) (checked : checkTaskReady environment request task = true) :
    (expand environment request task).unresolved = [] := by
  cases task with
  | start =>
      simp only [checkTaskReady] at checked
      rw [expand.eq_1]
      split
      · simp_all
      · rfl
  | rows frame =>
      rw [expand.eq_2]
      split
      · rfl
      · split <;> rfl
  | arguments frame =>
      rw [expand.eq_3]
      unfold expandArguments
      split
      · split <;> rfl
      · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
        cases mode with
        | input =>
            have projected : (instantiateAt? request.context.rule request.context.spec
                request.context.bound.length (request.context.site frame.index) [] 0
                frame.assignment schema).isSome = true := by
              simpa only [checkTaskReady, schemasFound, valuesFound, modesFound] using checked
            dsimp only
            split
            · simp_all
            · split <;> rfl
        | output => rfl
      · cases schemas : frame.schemas <;> cases values : frame.values <;>
          cases modes : frame.modes <;> simp_all [checkTaskReady]
  | matcher frame =>
      rw [expand.eq_4]
      unfold expandMatcher
      split
      · rfl
      · split <;> rfl

end Query

namespace Execution

def checkGoalReady (environment : Environment) : Goal → Bool
  | .premise context premise initial =>
      match premise with
      | .relationQuery _ _ => true
      | .freshness condition =>
          (freshnessSubject? context.rule context.spec context.bound context.premiseIndex
            context.quantifierDepth initial condition).isSome
      | .forAll collection _ _ =>
          (finiteCollection? context.bound.length initial collection).isSome
      | .congruence source _ =>
          (sourceType? environment.language context.rule source).isSome &&
            (instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source).isSome
      | .scopedStep step =>
          (instantiateAt? context.rule context.spec context.bound.length
            (context.site 0) [] step.binders.length initial step.source).isSome
  | .premises _ _ _ => true
  | .quantified context parameter _ _ elements initial =>
      match elements with
      | [] => true
      | element :: _ => checkTypedAssignment environment context.quantified
          (bindParameter parameter (localValue context.bound element) initial)
  | .root bound type source index =>
      match environment.language.rewrites[index]?, specification? environment index with
      | some rule, some spec => admittedFor rule spec &&
          checkOpenPatternWellSorted environment.language environment.free bound type source
      | _, _ => false
  | .steps _ _ _ _ => true

def checkDeliveredReady (environment : Environment) {outer goal : Goal}
    (result : Result environment goal) : Continuation environment goal outer → Bool
  | .rootBody bound _ _ _ rule spec _ _ _ _ _ _ _ _ _ =>
      match result with
      | .premises completed _ _ =>
          (reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
            rule spec bound.length completed).isSome
  | _ => true

def checkTaskReady (environment : Environment) (outer : Goal) : Task environment outer → Bool
  | .evaluate goal _ => checkGoalReady environment goal
  | .deliver result tail => checkDeliveredReady environment result tail
  | .query request state cursor _ =>
      state.unresolved.isEmpty &&
        match state.answers[cursor]?, state.agenda with
        | some _, _ => true
        | none, [] => true
        | none, task :: _ => Query.checkTaskReady environment request task
  | .rootMatch _ | .targetMatch _ | .scanChildren _ _ _ _ _ _ => true

theorem checkGoalReady_sound (environment : Environment) (outer goal : Goal)
    (tail : Continuation environment goal outer)
    (checked : checkGoalReady environment goal = true) :
    (evaluate environment outer goal tail).unresolved = [] := by
  cases goal with
  | premise context premise initial =>
      rw [evaluate.eq_1]
      cases premise with
      | relationQuery relation arguments => rfl
      | freshness condition =>
          simp only [checkGoalReady] at checked
          rw [evaluatePremise.eq_2]
          split
          · simp_all
          · split <;> rfl
      | forAll collection parameter body =>
          simp only [checkGoalReady] at checked
          rw [evaluatePremise.eq_3]
          split <;> simp_all
      | congruence source target =>
          simp only [checkGoalReady, Bool.and_eq_true] at checked
          rw [evaluatePremise.eq_4]
          split
          · simp_all
          · split <;> simp_all
      | scopedStep step =>
          simp only [checkGoalReady] at checked
          rw [evaluatePremise.eq_5]
          split <;> simp_all
  | premises context premises initial =>
      cases premises <;> rfl
  | quantified context parameter body index elements initial =>
      cases elements with
      | nil => rfl
      | cons element elements =>
          simp only [checkGoalReady] at checked
          rw [evaluate.eq_5]
          simp only [checked, ↓reduceDIte]
  | root bound type source index =>
      simp only [checkGoalReady] at checked
      rw [evaluate.eq_6, evaluateRoot.eq_1]
      split
      · simp_all
      · split
        · simp_all
        · simp_all only [Bool.and_eq_true]
          split <;> simp_all
  | steps bound type source limit => rfl

theorem checkDeliveredReady_sound (environment : Environment) {outer goal : Goal}
    (result : Result environment goal) (tail : Continuation environment goal outer)
    (checked : checkDeliveredReady environment result tail = true) :
    (delivered environment outer result tail).unresolved = [] := by
  cases tail with
  | done => rfl
  | nextPremise => cases result; rfl
  | prepend => cases result; rfl
  | quantifier => cases result; rfl
  | element => cases result; rfl
  | prependElement => cases result; rfl
  | rootBody =>
      cases result with
      | premises completed history valid =>
          simp only [checkDeliveredReady] at checked
          rw [delivered.eq_7]
          split
          · simp_all
          · split <;> rfl
  | searchedRoot => cases result; rfl
  | stepped => cases result; rfl

theorem checkTaskReady_sound (environment : Environment) (outer : Goal)
    (task : Task environment outer) (checked : checkTaskReady environment outer task = true) :
    (expand environment outer task).unresolved = [] := by
  cases task with
  | evaluate goal tail => exact checkGoalReady_sound environment outer goal tail checked
  | deliver result tail => exact checkDeliveredReady_sound environment result tail checked
  | query request state cursor tail =>
      have empty : state.unresolved = [] := by
        simp only [checkTaskReady, Bool.and_eq_true, List.isEmpty_iff] at checked
        exact checked.1
      simp only [expand, expandQuery]
      split
      · rfl
      · split
        · simp only [empty, List.map_nil]
        · rfl
  | rootMatch frame =>
      simp only [expand, expandRootMatch]
      split
      · split <;> rfl
      · split <;> rfl
  | targetMatch frame =>
      simp only [expand, expandTargetMatch]
      split
      · split <;> rfl
      · split <;> rfl
  | scanChildren bound type source limit cursor tail =>
      simp only [expand]
      split <;> rfl

mutual
  def checkTreeReady (environment : Environment) (outer : Goal)
      {task : Task environment outer} : Tree environment outer task → Bool
    | .branch children => checkTaskReady environment outer task && checkForestReady environment outer children

  def checkForestReady (environment : Environment) (outer : Goal)
      {tasks : List (Task environment outer)} :
      Scheduler.TaskForest (expand environment outer) tasks → Bool
    | .nil => true
    | .cons head tail => checkTreeReady environment outer head && checkForestReady environment outer tail
end

mutual
  theorem checkTreeReady_sound (environment : Environment) (outer : Goal)
      {task : Task environment outer} (tree : Tree environment outer task)
      (checked : checkTreeReady environment outer tree = true) : tree.obligations = [] :=
    match tree with
    | .branch children => by
        simp only [checkTreeReady, Bool.and_eq_true] at checked
        simp only [Scheduler.TaskTree.obligations,
          checkTaskReady_sound environment outer task checked.1,
          checkForestReady_sound environment outer children checked.2, List.nil_append]
  termination_by 2 * tree.cost
  decreasing_by simp only [Scheduler.TaskTree.cost]; omega

  theorem checkForestReady_sound (environment : Environment) (outer : Goal)
      {tasks : List (Task environment outer)}
      (forest : Scheduler.TaskForest (expand environment outer) tasks)
      (checked : checkForestReady environment outer forest = true) : forest.obligations = [] :=
    match forest with
    | .nil => rfl
    | .cons head tail => by
        simp only [checkForestReady, Bool.and_eq_true] at checked
        simp only [Scheduler.TaskForest.obligations,
          checkTreeReady_sound environment outer head checked.1,
          checkForestReady_sound environment outer tail checked.2, List.nil_append]
  termination_by 2 * forest.cost + 1
  decreasing_by
    all_goals simp only [Scheduler.TaskForest.cost]
    all_goals have positive : 0 < head.cost := by cases head; simp only [Scheduler.TaskTree.cost]; omega
    all_goals omega
end

def checkFinishReady (environment : Environment) (goal : Goal) : Bool :=
  checkTreeReady environment goal (treeStart environment goal)

theorem checkFinishReady_sound (environment : Environment) (goal : Goal)
    (checked : checkFinishReady environment goal = true) :
    (finish environment goal).unresolved = [] ∧
      complete environment goal (finish environment goal) = true := by
  have empty := (finish_obligations environment goal).trans
    (checkTreeReady_sound environment goal (treeStart environment goal) checked)
  refine ⟨empty, ?_⟩
  simp only [complete, Scheduler.complete, finish_settled, empty, List.isEmpty_nil,
    Bool.and_self]

end Execution
end Mettapedia.OSLF.MeTTaIL.GeneralPremise
