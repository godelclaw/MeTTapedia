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

variable {matcher : MatchingExecution}

def resultFreeWithin (footprint : List String) {environment : Environment} {goal : Goal}
    (result : Interpreted.Result matcher environment goal) : Prop :=
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
    {goal outer : Goal} → Interpreted.Continuation matcher environment goal outer → Prop
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
    Interpreted.Task matcher environment outer → Prop
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
    (state : State environment goal matcher) : Prop :=
  (∀ task ∈ state.agenda, taskFreeWithin footprint task) ∧
  (∀ result ∈ state.answers, resultFreeWithin footprint result)

/-- What an expansion's tasks and answers must satisfy. -/
def ExpansionFreeWithin (footprint : List String) {environment : Environment} {outer : Goal}
    (expansion : Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation) : Prop :=
  (∀ task ∈ expansion.tasks, taskFreeWithin footprint task) ∧
  (∀ answer ∈ expansion.answers, resultFreeWithin footprint answer)

theorem delivered_free_within (footprint : List String) (environment : Environment)
    (outer : Goal) {goal : Goal} (result : Interpreted.Result matcher environment goal)
    (tail : Interpreted.Continuation matcher environment goal outer)
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
    (tail : Interpreted.Continuation matcher environment (.premise depth context premise initial) outer)
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
    (tail : Interpreted.Continuation matcher environment (.root depth bound type source index) outer)
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
    (outer goal : Goal) (tail : Interpreted.Continuation matcher environment goal outer)
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

theorem root_match_expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (outer : Goal) (frame : RootMatchFrame environment outer matcher)
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
    · have captured := MatchingExecution.answer_free_within support _ frame.state frame.reachable answer
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

theorem target_match_expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (outer : Goal) (frame : TargetMatchFrame environment outer matcher)
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
    · have final := MatchingExecution.answer_free_within support _ frame.state frame.reachable answer
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

theorem query_expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (outer : Goal) (depth : Nat) (request : Query.Request) (state : Query.State environment request matcher) (cursor : Nat)
    (tail : Interpreted.Continuation matcher environment
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
        exact ⟨initial, Query.tick_free_within support footprint environment request provider dynamic state query, continued⟩
      · intro answer member; cases member

theorem expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment) (outer : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (task : Interpreted.Task matcher environment outer) (covered : taskFreeWithin footprint task) :
    ExpansionFreeWithin footprint (expand environment outer task) := by
  cases task with
  | evaluate goal tail => exact evaluate_free_within footprint environment outer goal tail covered.1 covered.2
  | deliver result tail => exact delivered_free_within footprint environment outer result tail covered.1 covered.2
  | query depth request state cursor tail =>
      exact query_expansion_free_within support footprint environment outer depth request state cursor tail provider dynamic
        covered.1 covered.2.1 covered.2.2
  | rootMatch frame => exact root_match_expansion_free_within support footprint environment outer frame covered.1 covered.2
  | targetMatch frame =>
      exact target_match_expansion_free_within support footprint environment outer frame covered.1 covered.2.1
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

theorem tick_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment) (goal : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (state : State environment goal matcher) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (tick environment goal state) :=
  Scheduler.tick_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (expand environment goal) (expansion_free_within support footprint environment goal provider dynamic) state covered

theorem run_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment) (goal : Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (fuel : Nat) (state : State environment goal matcher) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (run environment goal fuel state) :=
  Scheduler.run_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (expand environment goal) (expansion_free_within support footprint environment goal provider dynamic) fuel state covered

theorem start_free_within (footprint : List String) (environment : Environment) (goal : Goal)
    (initial : goalFreeWithin footprint goal) :
    stateFreeWithin footprint environment goal (start environment goal matcher) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨initial, initial⟩
  · intro result member; cases member



#print axioms delivered_free_within
#print axioms evaluate_premise_free_within
#print axioms evaluate_root_free_within
#print axioms evaluate_free_within
#print axioms root_match_expansion_free_within
#print axioms target_match_expansion_free_within
#print axioms query_expansion_free_within
#print axioms expansion_free_within
#print axioms tick_free_within
#print axioms run_free_within
#print axioms start_free_within

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled


namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

open Syntax RuleBinding ScopedRuleMatching GeneralPremise

variable {table : List String}

theorem removed_parameter_covered (parameter : String) {assignment : Assignment}
    (covered : AssignmentCovered table assignment) : AssignmentCovered table (removeParameter parameter assignment) := by
  induction assignment with
  | nil => intro entry member; cases member
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      simp only [removeParameter]
      split
      · exact ih (fun entry member => covered entry (List.mem_cons_of_mem _ member))
      · intro entry member
        rcases List.mem_cons.mp member with rfl | later
        · exact covered _ List.mem_cons_self
        · exact ih (fun entry member => covered entry (List.mem_cons_of_mem _ member)) entry later

theorem bound_parameter_covered (parameter : String) {assignment : Assignment} {value : ContextualValue}
    (covered : AssignmentCovered table assignment) (inserted : Covered table value.body) :
    AssignmentCovered table (bindParameter parameter value assignment) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | later
  · exact inserted
  · exact removed_parameter_covered parameter covered entry later

theorem finite_collection_covered {ambient : Nat} {assignment : Assignment} {name : String}
    {kind : CollType} {elements : List Pattern}
    (covered : AssignmentCovered table assignment)
    (read : finiteCollection? ambient assignment name = some (kind, elements)) : PatternsCovered table elements := by
  unfold finiteCollection? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨value, found, actual, instantiated, read⟩ := read
  have actualCovered := instantiateValue_covered (covered _ (lookup_member assignment name value found))
    (by intro argument member; cases member) instantiated
  unfold concreteCollection? at read
  split at read <;> cases read
  exact covered_elements.mp (fun name occurs => actualCovered name (List.mem_append_left _ occurs))

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open CanonicalCompare CanonicalCompare.AllNameSupport
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {matcher : MatchingExecution} {table footprint : List String}

/-- Only query instantiation compares an unchecked template result with the name table.
Root and child matching targets are checked object patterns at their matching boundaries. -/
def PremiseCovered (table : List String) : Premise → Prop
  | .relationQuery _ arguments => PatternsCovered table arguments
  | .forAll _ _ body => PremiseCovered table body
  | .freshness _ | .congruence _ _ | .scopedStep _ => True

def GoalCovered (table : List String) : Goal → Prop
  | .premise _ context premise initial => AssignmentCovered table initial ∧
      SpecificationCovered table context.spec ∧ PremiseCovered table premise
  | .premises _ context premises initial => AssignmentCovered table initial ∧
      SpecificationCovered table context.spec ∧ ∀ premise ∈ premises, PremiseCovered table premise
  | .quantified _ context _ body _ elements initial => AssignmentCovered table initial ∧
      SpecificationCovered table context.spec ∧ PremiseCovered table body ∧ PatternsCovered table elements
  | .root .. | .steps .. => True

def ResultCovered {environment : Environment} {goal : Goal} : Interpreted.Result matcher environment goal → Prop
  | .premise assignment _ _ | .premises assignment _ _ | .quantified assignment _ _ => AssignmentCovered table assignment
  | .root _ captured completed _ _ _ | .steps _ _ captured completed _ _ _ _ =>
      AssignmentCovered table captured ∧ AssignmentCovered table completed

def StepCallCovered {environment : Environment} (call : StepCall environment matcher) : Prop :=
  AssignmentCovered table call.initial ∧ SpecificationCovered table call.context.spec ∧
    PremiseCovered table call.premise

def ContinuationCovered {environment : Environment} :
    {goal outer : Goal} → Interpreted.Continuation matcher environment goal outer → Prop
  | _, _, .done _ => True
  | _, _, .nextPremise depth context premise premises initial tail =>
      GoalCovered table (.premises depth context (premise :: premises) initial) ∧ ContinuationCovered tail
  | _, _, .prepend depth context premise premises initial middle _ _ tail =>
      GoalCovered table (.premises depth context (premise :: premises) initial) ∧
        AssignmentCovered table middle ∧ ContinuationCovered tail
  | _, _, .quantifier depth context collection parameter body initial _ elements _ tail =>
      GoalCovered table (.premise depth context (.forAll collection parameter body) initial) ∧
        PatternsCovered table elements ∧ ContinuationCovered tail
  | _, _, .element depth context parameter body index element elements initial _ tail =>
      GoalCovered table (.quantified depth context parameter body index (element :: elements) initial) ∧
        ContinuationCovered tail
  | _, _, .prependElement depth context parameter body index element elements initial middle _ _ _ tail =>
      GoalCovered table (.quantified depth context parameter body index (element :: elements) initial) ∧
        AssignmentCovered table middle ∧ ContinuationCovered tail
  | _, _, .rootBody _ _ _ _ _ _ _ _ _ _ _ _ captured _ _ tail =>
      AssignmentCovered table captured ∧ ContinuationCovered tail
  | _, _, .searchedRoot _ _ _ _ _ _ _ tail => ContinuationCovered tail
  | _, _, .stepped _ call tail => StepCallCovered (table := table) call ∧ ContinuationCovered tail

def TaskCovered {environment : Environment} {outer : Goal} : Interpreted.Task matcher environment outer → Prop
  | .evaluate goal tail => GoalCovered table goal ∧ ContinuationCovered (table := table) tail
  | .deliver result tail => ResultCovered (table := table) result ∧ ContinuationCovered (table := table) tail
  | .query _ request state _ tail => SpecificationCovered table request.context.spec ∧
      PatternsCovered table request.arguments ∧ Query.NameSupport.StateCovered (table := table) environment request state ∧
      ContinuationCovered (table := table) tail
  | .rootMatch frame => ContinuationCovered (table := table) frame.tail
  | .targetMatch frame => StepCallCovered (table := table) frame.call ∧ AssignmentCovered table frame.captured ∧
      AssignmentCovered table frame.completed ∧ ContinuationCovered (table := table) frame.tail
  | .scanChildren _ _ _ _ _ _ tail => ContinuationCovered (table := table) tail

def StateCovered (environment : Environment) (outer : Goal) (state : State environment outer matcher) : Prop :=
  (∀ task ∈ state.agenda, TaskCovered (table := table) task) ∧
    (∀ result ∈ state.answers, ResultCovered (table := table) result)

def ExpansionCovered {environment : Environment} {outer : Goal}
    (expansion : Scheduler.Expansion (Interpreted.Task matcher environment outer)
      (Interpreted.Result matcher environment outer) Obligation) : Prop :=
  (∀ task ∈ expansion.tasks, TaskCovered (table := table) task) ∧
    (∀ result ∈ expansion.answers, ResultCovered (table := table) result)

theorem delivered_covered (environment : Environment) (outer : Goal) {goal : Goal}
    (result : Interpreted.Result matcher environment goal)
    (tail : Interpreted.Continuation matcher environment goal outer)
    (produced : ResultCovered (table := table) result) (continued : ContinuationCovered (table := table) tail) :
    ExpansionCovered (table := table) (delivered environment outer result tail) := by
  cases tail with
  | done goal =>
      constructor
      · intro task member; cases member
      · intro result member
        rcases List.mem_singleton.mp member with rfl
        exact produced
  | nextPremise depth context premise premises initial tail =>
      cases result with
      | premise assignment event valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨produced, continued.1.2.1,
              fun premise member => continued.1.2.2 premise (List.mem_cons_of_mem _ member)⟩,
              continued.1, produced, continued.2⟩
          · intro result member; cases member
  | prepend depth context premise premises initial middle event head tail =>
      cases result with
      | premises assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨produced, continued.2.2⟩
          · intro result member; cases member
  | quantifier depth context collection parameter body initial kind elements read tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨produced, continued.2.2⟩
          · intro result member; cases member
  | element depth context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise assignment event valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1.1, continued.1.2.1, continued.1.2.2.1,
              fun element member => continued.1.2.2.2 element (List.mem_cons_of_mem _ member)⟩,
              continued.1, produced, continued.2⟩
          · intro result member; cases member
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨produced, continued.2.2⟩
          · intro result member; cases member
  | rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched capturedTyped tail =>
      cases result with
      | premises assignment events valid =>
          simp only [delivered]
          split
          · constructor <;> intro item member <;> cases member
          · split
            · constructor
              · intro task member
                rcases List.mem_singleton.mp member with rfl
                exact ⟨⟨continued.1, produced⟩, continued.2⟩
              · intro result member; cases member
            · constructor <;> intro item member <;> cases member
  | searchedRoot depth bound type source index limit earlier tail =>
      cases result with
      | root trace captured completed events target valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨produced, continued⟩
          · intro result member; cases member
  | stepped depth call tail =>
      cases result with
      | steps index trace captured completed events target earlier valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨continued.1, produced.1, produced.2, continued.2⟩
          · intro result member; cases member

theorem evaluate_premise_covered (environment : Environment) (outer : Goal) (depth : Nat) (context : Context)
    (premise : Premise) (initial : Assignment)
    (tail : Interpreted.Continuation matcher environment (.premise depth context premise initial) outer)
    (covered : GoalCovered table (.premise depth context premise initial))
    (continued : ContinuationCovered (table := table) tail) :
    ExpansionCovered (table := table) (evaluatePremise environment outer depth context premise initial tail) := by
  cases premise with
  | relationQuery relation arguments =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨covered.2.1, covered.2.2,
          Query.NameSupport.start_covered environment _ covered.1, continued⟩
      · intro result member; cases member
  | freshness condition =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered.1, continued⟩
          · intro result member; cases member
        · constructor <;> intro item member <;> cases member
  | forAll collection parameter body =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i kind elements read
        have elementsCovered := finite_collection_covered covered.1 read
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨⟨covered.1, covered.2.1, covered.2.2, elementsCovered⟩,
            covered, elementsCovered, continued⟩
        · intro result member; cases member
  | congruence source target =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor <;> intro item member <;> cases member
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨trivial, ⟨covered.1, covered.2.1, trivial⟩, continued⟩
          · intro result member; cases member
  | scopedStep step =>
      simp only [evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨trivial, ⟨covered.1, covered.2.1, trivial⟩, continued⟩
        · intro result member; cases member

theorem evaluate_root_covered (environment : Environment) (outer : Goal) (depth : Nat)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Interpreted.Continuation matcher environment (.root depth bound type source index) outer)
    (continued : ContinuationCovered (table := table) tail) :
    ExpansionCovered (table := table) (evaluateRoot environment outer depth bound type source index tail) := by
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
              exact continued
            · intro result member; cases member
          · constructor <;> intro item member <;> cases member
        · constructor <;> intro item member <;> cases member

theorem evaluate_covered (environment : Environment) (outer : Goal) (goal : Goal)
    (tail : Interpreted.Continuation matcher environment goal outer)
    (covered : GoalCovered table goal) (continued : ContinuationCovered (table := table) tail) :
    ExpansionCovered (table := table) (evaluate environment outer goal tail) := by
  cases goal with
  | premise depth context premise initial => exact evaluate_premise_covered environment outer depth context premise initial tail covered continued
  | premises depth context premises initial =>
      cases premises with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered.1, continued⟩
          · intro result member; cases member
      | cons premise premises =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨covered.1, covered.2.1, covered.2.2 premise List.mem_cons_self⟩, covered, continued⟩
          · intro result member; cases member
  | quantified depth context parameter body index elements initial =>
      cases elements with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered.1, continued⟩
          · intro result member; cases member
      | cons element elements =>
          simp only [evaluate]
          split
          · have captured := bound_parameter_covered parameter (value := localValue context.bound element) covered.1
              (covered.2.2.2 element List.mem_cons_self)
            constructor
            · intro task member
              rcases List.mem_singleton.mp member with rfl
              exact ⟨⟨captured, covered.2.1, covered.2.2.1⟩, covered, continued⟩
            · intro result member; cases member
          · constructor <;> intro item member <;> cases member
  | root depth bound type source index => exact evaluate_root_covered environment outer depth bound type source index tail continued
  | steps depth bound type source limit =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact continued
      · intro result member; cases member

theorem selected_specification_covered (environment : Environment)
    (covered : ∀ entry ∈ environment.specifications, SpecificationCovered table entry.2)
    {index : Nat} {spec : RuleBindingSpec} (selected : specification? environment index = some spec) :
    SpecificationCovered table spec := by
  unfold specification? at selected
  cases found : environment.specifications.find? (fun entry => entry.1 == index) with
  | none => simp only [found, Option.map_none] at selected; cases selected
  | some entry =>
      simp only [found, Option.map_some, Option.some.injEq] at selected
      rw [← selected]
      exact covered entry (List.mem_of_find?_eq_some found)

theorem firing_target_covered (environment : Environment)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List matcher.Choice} {captured completed : Assignment} {history : List (Event matcher.Choice)}
    (fired : GeneralPremise.Interpreted.RootFiring matcher.meaning environment bound type source index
      trace captured completed history target)
    (free : ∀ name ∈ target.freeFvarNames, name ∈ footprint) : Covered table target := by
  cases fired with
  | fire _ _ _ _ _ _ _ _ typed =>
      exact TypedObjectAlphabet.wellSorted_covered typed declarations (fun name member => included name (free name member))

theorem root_match_expansion_covered (support : matcher.PreservesNames)
    (environment : Environment) (outer : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (templates : ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises, PremiseCovered table premise)
    (specifications : ∀ entry ∈ environment.specifications, SpecificationCovered table entry.2)
    (frame : RootMatchFrame environment outer matcher)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint)
    (continued : ContinuationCovered (table := table) frame.tail) :
    ExpansionCovered (table := table) (expandRootMatch environment outer frame) := by
  have sourceCovered := TypedObjectAlphabet.wellSorted_covered frame.sorted declarations
    (fun name member => included name (source name member))
  unfold expandRootMatch
  split
  · rename_i answer found
    dsimp only
    unfold continueRootAnswer
    dsimp only
    split
    · have captured := MatchingExecution.answer_covered support frame.reachable
        (List.mem_of_getElem? found) (by intro entry member; cases member) sourceCovered
      have spines := selected_specification_covered environment specifications frame.specified
      have premises := templates frame.rule (List.mem_of_getElem? frame.declared)
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨⟨captured, spines, premises⟩, captured, continued⟩
        · exact continued
      · intro result member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact continued
      · intro result member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact continued
      · intro result member; cases member

theorem target_match_expansion_covered (support : matcher.PreservesNames)
    (environment : Environment) (outer : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (frame : TargetMatchFrame environment outer matcher)
    (free : taskFreeWithin footprint (.targetMatch frame))
    (covered : TaskCovered (table := table) (.targetMatch frame)) :
    ExpansionCovered (table := table) (expandTargetMatch environment outer frame) := by
  have targetCovered := firing_target_covered environment declarations included frame.valid free.2.2.2.1
  unfold expandTargetMatch
  split
  · rename_i answer found
    split
    · have captured := MatchingExecution.answer_covered support frame.reachable
        (List.mem_of_getElem? found) covered.1.1 targetCovered
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨captured, covered.2.2.2⟩
        · exact covered
      · intro result member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact covered
      · intro result member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact covered
      · intro result member; cases member

theorem query_expansion_covered (support : matcher.PreservesNames) (freeSupport : matcher.PreservesFreeNames)
    (environment : Environment) (outer : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (depth : Nat) (request : Query.Request) (state : Query.State environment request matcher) (cursor : Nat)
    (tail : Interpreted.Continuation matcher environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : taskFreeWithin footprint (.query depth request state cursor tail))
    (covered : TaskCovered (table := table) (.query depth request state cursor tail)) :
    ExpansionCovered (table := table) (expandQuery environment outer depth request state cursor tail) := by
  unfold expandQuery
  split
  · rename_i answer found
    constructor
    · intro task member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨covered.2.2.1.2 answer (List.mem_of_getElem? found), covered.2.2.2⟩
      · exact covered
    · intro result member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · have next := Query.NameSupport.run_covered support freeSupport environment request declarations included provider dynamic
        covered.2.1 covered.1 1 state free.2.1 covered.2.2.1
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨covered.1, covered.2.1, next, covered.2.2.2⟩
      · intro result member; cases member

theorem expansion_covered (support : matcher.PreservesNames) (freeSupport : matcher.PreservesFreeNames)
    (environment : Environment) (outer : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (templates : ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises, PremiseCovered table premise)
    (specifications : ∀ entry ∈ environment.specifications, SpecificationCovered table entry.2)
    (task : Interpreted.Task matcher environment outer)
    (free : taskFreeWithin footprint task) (covered : TaskCovered (table := table) task) :
    ExpansionCovered (table := table) (expand environment outer task) := by
  cases task with
  | evaluate goal tail => exact evaluate_covered environment outer goal tail covered.1 covered.2
  | deliver result tail => exact delivered_covered environment outer result tail covered.1 covered.2
  | query depth request state cursor tail =>
      exact query_expansion_covered support freeSupport environment outer declarations included provider dynamic
        depth request state cursor tail free covered
  | rootMatch frame =>
      exact root_match_expansion_covered support environment outer declarations included templates specifications frame free.1 covered
  | targetMatch frame => exact target_match_expansion_covered support environment outer declarations included frame free covered
  | scanChildren depth bound type source limit cursor tail =>
      simp only [expand]
      split
      · constructor
        · intro task member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨trivial, covered⟩
          · exact covered
        · intro result member; cases member
      · constructor <;> intro item member <;> cases member

theorem run_covered (support : matcher.PreservesNames) (freeSupport : matcher.PreservesFreeNames)
    (environment : Environment) (outer : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (templates : ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises, PremiseCovered table premise)
    (specifications : ∀ entry ∈ environment.specifications, SpecificationCovered table entry.2)
    (fuel : Nat) (state : State environment outer matcher)
    (free : stateFreeWithin footprint environment outer state)
    (covered : StateCovered (table := table) environment outer state) :
    StateCovered (table := table) environment outer (run environment outer fuel state) := by
  let taskProperty : Interpreted.Task matcher environment outer → Prop :=
    fun task => taskFreeWithin footprint task ∧ TaskCovered (table := table) task
  let resultProperty : Interpreted.Result matcher environment outer → Prop :=
    fun result => resultFreeWithin footprint result ∧ ResultCovered (table := table) result
  have preserves : ∀ task, taskProperty task →
      (∀ next ∈ (expand environment outer task).tasks, taskProperty next) ∧
      (∀ result ∈ (expand environment outer task).answers, resultProperty result) := by
    intro task before
    have freeNext := expansion_free_within freeSupport footprint environment outer provider dynamic task before.1
    have namesNext := expansion_covered support freeSupport environment outer declarations included provider dynamic
      templates specifications task before.1 before.2
    exact ⟨fun next member => ⟨freeNext.1 next member, namesNext.1 next member⟩,
      fun result member => ⟨freeNext.2 result member, namesNext.2 result member⟩⟩
  have result := Scheduler.run_preserves taskProperty resultProperty (expand environment outer) preserves fuel state
    ⟨fun task member => ⟨free.1 task member, covered.1 task member⟩,
      fun result member => ⟨free.2 result member, covered.2 result member⟩⟩
  exact ⟨fun task member => (result.1 task member).2, fun answer member => (result.2 answer member).2⟩

theorem start_covered (environment : Environment) (goal : Goal) (seed : GoalCovered table goal) :
    StateCovered (table := table) environment goal (start environment goal matcher) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨seed, trivial⟩
  · intro result member; cases member



end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open CanonicalCompare CanonicalCompare.AllNameSupport

variable {matcher : MatchingExecution} {table footprint : List String}

theorem run_from_start_covered
    (support : matcher.PreservesNames) (freeSupport : matcher.PreservesFreeNames)
    (environment : Environment) (goal : Goal)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (templates : ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises, PremiseCovered table premise)
    (specifications : ∀ entry ∈ environment.specifications, SpecificationCovered table entry.2)
    (initialFree : goalFreeWithin footprint goal) (initial : GoalCovered table goal) (fuel : Nat) :
    StateCovered (table := table) environment goal
      (run environment goal fuel (start environment goal matcher)) :=
  run_covered support freeSupport environment goal declarations included provider dynamic templates specifications
    fuel _ (start_free_within footprint environment goal initialFree) (start_covered environment goal initial)

/-- Only unchecked query templates contribute static constructor or display names. -/
def queryTemplateNames : Premise → List String
  | .relationQuery _ arguments => namesList arguments
  | .forAll _ _ body => queryTemplateNames body
  | .freshness _ | .congruence _ _ | .scopedStep _ => []

theorem premise_covered_by_names (premise : Premise)
    (included : ∀ name ∈ queryTemplateNames premise, name ∈ table) : PremiseCovered table premise := by
  induction premise with
  | relationQuery relation arguments =>
      intro pattern member name occurs
      exact included name (mem_namesList.mpr ⟨pattern, member, occurs⟩)
  | forAll collection parameter body ih => exact ih included
  | freshness | congruence | scopedStep => trivial

def spineNames (spec : RuleBindingSpec) : List String :=
  spec.occurrences.flatMap fun occurrence => namesList occurrence.arguments

theorem specification_covered_by_names (spec : RuleBindingSpec)
    (included : ∀ name ∈ spineNames spec, name ∈ table) : SpecificationCovered table spec := by
  intro occurrence member pattern patternMember name occurs
  exact included name (List.mem_flatMap.mpr ⟨occurrence, member,
    mem_namesList.mpr ⟨pattern, patternMember, occurs⟩⟩)

/-- A finite snapshot includes metadata in authored query schemas and supplied occurrence spines. -/
def environmentNameSeeds (environment : Environment) (footprint : List String) : List String :=
  labels environment.language ++ footprint ++
    environment.language.rewrites.flatMap (fun rule => rule.premises.flatMap queryTemplateNames) ++
    environment.specifications.flatMap (fun entry => spineNames entry.2)

def environmentNameTable (environment : Environment) (footprint : List String) : List String :=
  nameTable (environmentNameSeeds environment footprint)

theorem environment_table_ordered (environment : Environment) (footprint : List String) :
    NameOrdered (environmentNameTable environment footprint) := nameTable_ordered _

theorem environment_table_declarations (environment : Environment) (footprint : List String) :
    ∀ rule ∈ environment.language.terms, rule.label ∈ environmentNameTable environment footprint := by
  intro rule member
  apply mem_nameTable.mpr
  simp only [environmentNameSeeds, List.mem_append]
  exact .inl (.inl (.inl (List.mem_map.mpr ⟨rule, member, rfl⟩)))

theorem environment_table_footprint (environment : Environment) (footprint : List String) :
    ∀ name ∈ footprint, name ∈ environmentNameTable environment footprint := by
  intro name member
  apply mem_nameTable.mpr
  simp only [environmentNameSeeds, List.mem_append]
  exact .inl (.inl (.inr member))

theorem environment_table_templates (environment : Environment) (footprint : List String) :
    ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises,
      PremiseCovered (environmentNameTable environment footprint) premise := by
  intro rule member premise premiseMember
  apply premise_covered_by_names
  intro name occurs
  apply mem_nameTable.mpr
  simp only [environmentNameSeeds, List.mem_append]
  exact .inl (.inr (List.mem_flatMap.mpr ⟨rule, member,
    List.mem_flatMap.mpr ⟨premise, premiseMember, occurs⟩⟩))

theorem environment_table_specifications (environment : Environment) (footprint : List String) :
    ∀ entry ∈ environment.specifications, SpecificationCovered (environmentNameTable environment footprint) entry.2 := by
  intro entry member
  apply specification_covered_by_names
  intro name occurs
  apply mem_nameTable.mpr
  simp only [environmentNameSeeds, List.mem_append]
  exact .inr (List.mem_flatMap.mpr ⟨entry, member, occurs⟩)

theorem ordinary_root_run_covered (environment : Environment) (depth : Nat)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index fuel : Nat)
    (dynamic : Query.DynamicOutputsFreeWithin (source.freeFvarNames ++ providerFreeNames environment.provider) environment) :
    StateCovered (table := environmentNameTable environment (source.freeFvarNames ++ providerFreeNames environment.provider))
      environment (.root depth bound type source index)
      (run environment (.root depth bound type source index) fuel
        (start environment (.root depth bound type source index) MatchingExecution.ordinary)) := by
  exact run_from_start_covered MatchingExecution.ordinary_preservesNames MatchingExecution.ordinary_preservesFreeNames
    environment (.root depth bound type source index)
    (environment_table_declarations _ _) (environment_table_footprint _ _)
    (provider_coverage_mono _ _ environment.provider (fun _ member => List.mem_append_right _ member)
      (provider_covered_by_own_names _)) dynamic
    (environment_table_templates _ _) (environment_table_specifications _ _)
    (fun _ member => List.mem_append_left _ member) trivial fuel


end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport

#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.removed_parameter_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.bound_parameter_covered
#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.finite_collection_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.PremiseCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.GoalCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.ResultCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.StepCallCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.ContinuationCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.TaskCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.StateCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.ExpansionCovered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.delivered_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.evaluate_premise_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.evaluate_root_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.evaluate_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.selected_specification_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.firing_target_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.root_match_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.target_match_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.query_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.run_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.start_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.run_from_start_covered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.queryTemplateNames
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.premise_covered_by_names
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.spineNames
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.specification_covered_by_names
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environmentNameSeeds
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environmentNameTable
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environment_table_ordered
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environment_table_declarations
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environment_table_footprint
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environment_table_templates
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.environment_table_specifications
#print axioms Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.NameSupport.ordinary_root_run_covered
