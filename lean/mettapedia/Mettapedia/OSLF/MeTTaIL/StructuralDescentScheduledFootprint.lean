import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage

/-!
# Free names of the scheduled descent machine stay within a footprint

A footprint is a list of free names. When the source, the initial assignments and the provider's
rows mention only names in the footprint, so does every task and answer the scheduled machine
reaches: matching, instantiation, collections and reducts introduce no new free names. A finite
snapshot of the free-type context on the footprint therefore answers every lookup a run makes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open ConditionalEquationExecution
open ScopedReflectiveExecution
open Substitution
open GeneralScopedMatchMachine

def goalFreeWithin (footprint : List String) : Goal → Prop
  | .premise _ context _ initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial
  | .premises _ context _ initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial
  | .quantified _ context _ _ _ elements initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial ∧ patternsFreeWithin footprint elements
  | .root _ _ _ source _ => ∀ name ∈ source.freeFvarNames, name ∈ footprint
  | .steps _ _ _ source _ => ∀ name ∈ source.freeFvarNames, name ∈ footprint

def resultFreeWithin (footprint : List String) {environment : Environment} {goal : Goal}
    (result : Result environment goal) : Prop :=
  goalFreeWithin footprint goal ∧
  match result with
  | .premise assignment _ _ => assignmentFreeWithin footprint assignment
  | .premises assignment _ _ => assignmentFreeWithin footprint assignment
  | .quantified assignment _ _ => assignmentFreeWithin footprint assignment
  | .root _ captured completed _ target _ => assignmentFreeWithin footprint captured ∧
      assignmentFreeWithin footprint completed ∧
      (∀ name ∈ target.freeFvarNames, name ∈ footprint)
  | .steps _ _ captured completed _ target _ _ => assignmentFreeWithin footprint captured ∧
      assignmentFreeWithin footprint completed ∧
      (∀ name ∈ target.freeFvarNames, name ∈ footprint)

def continuationFreeWithin (footprint : List String) {environment : Environment} :
    {goal outer : Goal} → Continuation environment goal outer → Prop
  | _, _, .done goal => goalFreeWithin footprint goal
  | _, _, .nextPremise depth context premise premises initial tail =>
      goalFreeWithin footprint (.premises depth context (premise :: premises) initial) ∧
      continuationFreeWithin footprint tail
  | _, _, .prepend depth context premise premises initial middle _ _ tail =>
      goalFreeWithin footprint (.premises depth context (premise :: premises) initial) ∧
      assignmentFreeWithin footprint middle ∧ continuationFreeWithin footprint tail
  | _, _, .quantifier depth context collection parameter body initial _ elements _ tail =>
      goalFreeWithin footprint (.premise depth context (.forAll collection parameter body) initial) ∧
      patternsFreeWithin footprint elements ∧ continuationFreeWithin footprint tail
  | _, _, .element depth context parameter body index element elements initial _ tail =>
      goalFreeWithin footprint (.quantified depth context parameter body index (element :: elements) initial) ∧
      continuationFreeWithin footprint tail
  | _, _, .prependElement depth context parameter body index element elements initial middle _ _ _ tail =>
      goalFreeWithin footprint (.quantified depth context parameter body index (element :: elements) initial) ∧
      assignmentFreeWithin footprint middle ∧ continuationFreeWithin footprint tail
  | _, _, .rootBody depth bound type source index _ _ _ _ _ _ _ captured _ _ tail =>
      goalFreeWithin footprint (.root (depth + 1) bound type source index) ∧
      assignmentFreeWithin footprint captured ∧ continuationFreeWithin footprint tail
  | _, _, .searchedRoot depth bound type source _ limit _ tail =>
      goalFreeWithin footprint (.steps depth bound type source limit) ∧ continuationFreeWithin footprint tail
  | _, _, .stepped _ call tail => Execution.stepCallFreeWithin footprint call ∧ continuationFreeWithin footprint tail

def taskFreeWithin (footprint : List String) {environment : Environment} {outer : Goal} :
    Task environment outer → Prop
  | .evaluate goal tail => goalFreeWithin footprint goal ∧ continuationFreeWithin footprint tail
  | .deliver result tail => resultFreeWithin footprint result ∧ continuationFreeWithin footprint tail
  | .query depth request state _ tail =>
      goalFreeWithin footprint (.premise depth request.context (.relationQuery request.relation request.arguments)
        request.initial) ∧
      Query.stateFreeWithin footprint environment request state ∧ continuationFreeWithin footprint tail
  | .rootMatch frame =>
      (∀ name ∈ frame.source.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint frame.tail
  | .targetMatch frame => Execution.stepCallFreeWithin footprint frame.call ∧
      assignmentFreeWithin footprint frame.captured ∧ assignmentFreeWithin footprint frame.completed ∧
      (∀ name ∈ frame.target.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint frame.tail
  | .scanChildren _ _ _ source _ _ tail =>
      (∀ name ∈ source.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint tail

def stateFreeWithin (footprint : List String) (environment : Environment) (goal : Goal)
    (state : State environment goal) : Prop :=
  (∀ task ∈ state.agenda, taskFreeWithin footprint task) ∧
  (∀ result ∈ state.answers, resultFreeWithin footprint result)

/-- What an expansion's tasks and answers must satisfy. -/
def ExpansionFreeWithin (footprint : List String) {environment : Environment} {outer : Goal}
    (expansion : Scheduler.Expansion (Task environment outer) (Result environment outer) Obligation) : Prop :=
  (∀ task ∈ expansion.tasks, taskFreeWithin footprint task) ∧
  (∀ answer ∈ expansion.answers, resultFreeWithin footprint answer)

theorem delivered_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) {goal : Goal} (result : Result environment goal)
    (tail : Continuation environment goal outer)
    (produced : resultFreeWithin footprint result) (continued : continuationFreeWithin footprint tail) :
    ExpansionFreeWithin footprint (delivered environment outer result tail) := by
  cases tail with
  | done goal =>
      constructor
      · intro task member; cases member
      · intro answer member
        rcases List.mem_singleton.mp member with rfl
        exact produced
  | nextPremise depth context premise premises initial tail =>
      cases result with
      | premise assignment event valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨produced.1.1, produced.2⟩, continued.1, produced.2, continued.2⟩
          · intro answer member; cases member
  | prepend depth context premise premises initial middle event head tail =>
      cases result with
      | premises assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | quantifier depth context collection parameter body initial kind elements read tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | element depth context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise assignment event valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            refine ⟨⟨continued.1.1, continued.1.2.1, ?_⟩, continued.1, produced.2, continued.2⟩
            intro pattern member name occurs
            exact continued.1.2.2 pattern (List.mem_cons_of_mem _ member) name occurs
          · intro answer member; cases member
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
      capturedTyped tail =>
      cases result with
      | premises assignment events valid =>
          simp only [delivered]
          split
          · constructor <;> intro item member <;> cases member
          · rename_i target converted
            split
            · have covered := selected_reduct_free_within footprint environment.reflection rule spec admitted
                bound.length assignment target produced.2 converted
              constructor
              · intro task member
                rcases List.mem_singleton.mp member with rfl
                exact ⟨⟨continued.1, continued.2.1, produced.2, covered⟩, continued.2.2⟩
              · intro answer member; cases member
            · constructor <;> intro item member <;> cases member
  | searchedRoot depth bound type source index limit earlier tail =>
      cases result with
      | root trace captured completed events target valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2⟩
          · intro answer member; cases member
  | stepped depth call tail =>
      cases result with
      | steps index trace captured completed events target earlier valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨continued.1, produced.2.1, produced.2.2.1, produced.2.2.2, continued.2⟩
          · intro answer member; cases member

theorem evaluate_premise_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) (depth : Nat) (context : Context) (premise : Premise) (initial : Assignment)
    (tail : Continuation environment (.premise depth context premise initial) outer)
    (admitted : admittedFor context.rule context.spec = true)
    (stored : assignmentFreeWithin footprint initial)
    (continued : continuationFreeWithin footprint tail) :
    ExpansionFreeWithin footprint (evaluatePremise environment outer depth context premise initial tail) := by
  cases premise with
  | relationQuery relation arguments =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨⟨admitted, stored⟩, Query.start_free_within footprint environment _ stored, continued⟩
      · intro answer member; cases member
  | freshness condition =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨⟨admitted, stored⟩, stored⟩, continued⟩
          · intro answer member; cases member
        · constructor <;> intro item member <;> cases member
  | forAll collection parameter body =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i kind elements read
        have elementsCovered := Query.finite_collection_free_within footprint context.bound.length initial
          collection kind elements stored read
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨⟨admitted, stored, elementsCovered⟩, ⟨admitted, stored⟩, elementsCovered, continued⟩
        · intro answer member; cases member
  | congruence source target =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor <;> intro item member <;> cases member
        · rename_i actual interpreted
          have actualCovered := admitted_instantiate_with_free_within footprint Substitution.instantiateBVar
            (instantiate_bvar_free_within footprint) context.rule context.spec admitted context.bound.length
            (context.site 0) [] 0 initial source actual stored interpreted
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨actualCovered, ⟨admitted, stored, actualCovered⟩, continued⟩
          · intro answer member; cases member
  | scopedStep step =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i actual interpreted
        have actualCovered := admitted_instantiate_with_free_within footprint Substitution.instantiateBVar
          (instantiate_bvar_free_within footprint) context.rule context.spec admitted context.bound.length
          (context.site 0) [] step.binders.length initial step.source actual stored interpreted
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨actualCovered, ⟨admitted, stored, actualCovered⟩, continued⟩
        · intro answer member; cases member

theorem evaluate_root_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Continuation environment (.root depth bound type source index) outer)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint tail) :
    ExpansionFreeWithin footprint (evaluateRoot environment outer depth bound type source index tail) := by
  unfold evaluateRoot
  split
  · constructor <;> intro item member <;> cases member
  · split
    · constructor <;> intro item member <;> cases member
    · split
      · constructor <;> intro item member <;> cases member
      · split
        · split
          · constructor
            · intro task member
              rcases List.mem_singleton.mp member with rfl
              exact ⟨covered, continued⟩
            · intro answer member; cases member
          · constructor <;> intro item member <;> cases member
        · constructor <;> intro item member <;> cases member

theorem evaluate_free_within (footprint : List String) (environment : Environment)
    (outer goal : Goal) (tail : Continuation environment goal outer)
    (covered : goalFreeWithin footprint goal) (continued : continuationFreeWithin footprint tail) :
    ExpansionFreeWithin footprint (evaluate environment outer goal tail) := by
  cases goal with
  | premise depth context premise initial =>
      exact evaluate_premise_free_within footprint environment outer depth context premise initial tail covered.1
        covered.2 continued
  | premises depth context premises initial =>
      cases premises with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨covered, covered.2⟩, continued⟩
          · intro answer member; cases member
      | cons premise premises =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered, covered, continued⟩
          · intro answer member; cases member
  | quantified depth context parameter body index elements initial =>
      cases elements with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨covered, covered.2.1⟩, continued⟩
          · intro answer member; cases member
      | cons element elements =>
          simp only [evaluate]
          split
          · have boundCovered := Query.bound_parameter_free_within footprint parameter
              (localValue context.bound element) initial covered.2.1 (covered.2.2 element (by simp))
            constructor
            · intro task member
              rcases List.mem_singleton.mp member with rfl
              exact ⟨⟨covered.1, boundCovered⟩, covered, continued⟩
            · intro answer member; cases member
          · constructor <;> intro item member <;> cases member
  | root depth bound type source index =>
      exact evaluate_root_free_within footprint environment outer depth bound type source index tail covered continued
  | steps depth bound type source limit =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨covered, continued⟩
      · intro answer member; cases member

theorem root_match_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) (frame : RootMatchFrame environment outer)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint frame.tail) :
    ExpansionFreeWithin footprint (expandRootMatch environment outer frame) := by
  unfold expandRootMatch
  split
  · rename_i answer found
    dsimp only
    unfold continueRootAnswer
    dsimp only
    split
    · have captured := matcher_answer_free_within _ frame.state frame.reachable answer
        (List.mem_of_getElem? found) footprint (by intro entry member; cases member) source
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨⟨frame.admitted, captured⟩, source, captured, continued⟩
        · exact ⟨source, continued⟩
      · intro answer member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨source, continued⟩
      · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨source, continued⟩
      · intro answer member; cases member

theorem target_match_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) (frame : TargetMatchFrame environment outer)
    (call : Execution.stepCallFreeWithin footprint frame.call)
    (captured : assignmentFreeWithin footprint frame.captured)
    (completed : assignmentFreeWithin footprint frame.completed)
    (target : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint frame.tail) :
    ExpansionFreeWithin footprint (expandTargetMatch environment outer frame) := by
  unfold expandTargetMatch
  split
  · rename_i answer found
    split
    · have final := matcher_answer_free_within _ frame.state frame.reachable answer
        (List.mem_of_getElem? found) footprint call.2.1 target
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨⟨⟨call.1, call.2.1⟩, final⟩, continued⟩
        · exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member

theorem query_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) (depth : Nat) (request : Query.Request) (state : Query.State environment request) (cursor : Nat)
    (tail : Continuation environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (initial : goalFreeWithin footprint
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial))
    (query : Query.stateFreeWithin footprint environment request state)
    (continued : continuationFreeWithin footprint tail) :
    ExpansionFreeWithin footprint (expandQuery environment outer depth request state cursor tail) := by
  unfold expandQuery
  split
  · rename_i answer found
    have stored := query.2 answer (List.mem_of_getElem? found)
    constructor
    · intro task member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨⟨initial, stored⟩, continued⟩
      · exact ⟨initial, query, continued⟩
    · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨initial, Query.tick_free_within footprint environment request provider dynamic state query, continued⟩
      · intro answer member; cases member

theorem expansion_free_within (footprint : List String) (environment : Environment) (outer : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (task : Task environment outer) (covered : taskFreeWithin footprint task) :
    ExpansionFreeWithin footprint (expand environment outer task) := by
  cases task with
  | evaluate goal tail => exact evaluate_free_within footprint environment outer goal tail covered.1 covered.2
  | deliver result tail => exact delivered_free_within footprint environment outer result tail covered.1 covered.2
  | query depth request state cursor tail =>
      exact query_expansion_free_within footprint environment outer depth request state cursor tail provider dynamic
        covered.1 covered.2.1 covered.2.2
  | rootMatch frame => exact root_match_expansion_free_within footprint environment outer frame covered.1 covered.2
  | targetMatch frame =>
      exact target_match_expansion_free_within footprint environment outer frame covered.1 covered.2.1
        covered.2.2.1 covered.2.2.2.1 covered.2.2.2.2
  | scanChildren depth bound type source limit cursor tail =>
      simp only [expand]
      split
      · constructor
        · intro next member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨covered.1, covered.1, covered.2⟩
          · exact covered
        · intro answer member; cases member
      · constructor <;> intro item member <;> cases member

theorem tick_free_within (footprint : List String) (environment : Environment) (goal : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (state : State environment goal) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (tick environment goal state) :=
  Scheduler.tick_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (expand environment goal) (expansion_free_within footprint environment goal provider dynamic) state covered

theorem run_free_within (footprint : List String) (environment : Environment) (goal : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (fuel : Nat) (state : State environment goal) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (run environment goal fuel state) :=
  Scheduler.run_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (expand environment goal) (expansion_free_within footprint environment goal provider dynamic) fuel state covered

theorem start_free_within (footprint : List String) (environment : Environment) (goal : Goal)
    (initial : goalFreeWithin footprint goal) :
    stateFreeWithin footprint environment goal (start environment goal) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨initial, initial⟩
  · intro result member; cases member

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
