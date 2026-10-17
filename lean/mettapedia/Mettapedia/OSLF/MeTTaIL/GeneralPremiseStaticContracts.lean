import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticReadiness
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalFlow

/-!
# Derived contracts for admitted continuation goals

The contracts retain typing, canonical captured bodies and finite/atomic
refinements. Each condition follows from authored syntax, declared provider
rows, and actual matching. No field asserts completeness or termination.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Availability is a property of a registered primitive on typed caller
inputs, independently of the continuation machine. A false response is an
available empty table; an unavailable response cannot establish resolution. -/
structure DynamicAvailability (environment : Environment) : Prop where
  query : ∀ (request : Query.Request) (signature : Signature),
    request.relation ∈ environment.provider.dynamicRelations →
    signature? environment.provider request.relation request.arguments.length = some signature →
    TypedAssignment environment request.context request.initial →
    ∀ resolved, DynamicInputs request.context 0 request.initial request.arguments signature.modes resolved →
      ∃ rows, environment.dynamic.Source request.relation resolved rows

/-- An ordinary finite provider does not need a native availability promise. -/
theorem DynamicAvailability.of_empty {environment : Environment}
    (empty : environment.provider.dynamicRelations = []) : DynamicAvailability environment := by
  constructor
  intro request signature registered
  simp only [empty, List.not_mem_nil] at registered


structure InputFacts (environment : Environment) (context : Context)
    (refinement : Refinement) (assignment : Assignment) : Prop where
  typed : TypedAssignment environment context assignment
  canonical : CanonicalValues assignment
  represented : refinement.Holds assignment

def localRefinement (refinement : Refinement) (parameter : String) : Refinement :=
  ⟨parameter :: refinement.available, refinement.finite.filter (· != parameter),
    refinement.atomic.filter (· != parameter)⟩

inductive GoalAdmitted (environment : Environment) : Execution.Goal → Type where
  | premise {context : Context} {premise : Premise} {assignment : Assignment}
      (refinement : Refinement)
      (facts : InputFacts environment context refinement assignment)
      (zero : checkZeroDependencies context.spec = true)
      (supported : (premiseFlow environment.language environment.provider context.rule context.spec
        context.premiseIndex context.quantifierDepth refinement premise).supported = true)
      (stratum : context.ruleIndex ≤ environment.language.rewrites.length) :
      GoalAdmitted environment (.premise context premise assignment)
  | premises {context : Context} {premises : List Premise} {assignment : Assignment}
      (refinement : Refinement)
      (facts : InputFacts environment context refinement assignment)
      (zero : checkZeroDependencies context.spec = true)
      (depth : context.quantifierDepth = 0)
      (supported : (premisesFlow environment.language environment.provider context.rule context.spec
        context.premiseIndex refinement premises).supported = true)
      (stratum : context.ruleIndex ≤ environment.language.rewrites.length) :
      GoalAdmitted environment (.premises context premises assignment)
  | quantified {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {elements : List Pattern} {assignment : Assignment}
      (refinement : Refinement) (elementType : TypeExpr)
      (facts : InputFacts environment context refinement assignment)
      (zero : checkZeroDependencies context.spec = true)
      (parameterType : lookupRuleType? context.rule parameter = some elementType)
      (parameterDependencies : dependencies? context.spec parameter = some [])
      (elementsTyped : ElementsHaveType environment.language environment.free context.bound elements elementType)
      (elementsObjects : isObjectPatternList elements = true)
      (elementsCanonical : Pattern.hasCanonicalBinderMetadataList elements = true)
      (supported : (premiseFlow environment.language environment.provider context.rule context.spec
        context.premiseIndex (context.quantifierDepth + 1)
        (localRefinement refinement parameter) body).supported = true)
      (stratum : context.ruleIndex ≤ environment.language.rewrites.length) :
      GoalAdmitted environment (.quantified context parameter body index elements assignment)
  | root {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
      (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
      (declared : index < environment.language.rewrites.length) :
      GoalAdmitted environment (.root bound type source index)
  | steps {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {limit : Nat}
      (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
      (stratum : limit ≤ environment.language.rewrites.length) :
      GoalAdmitted environment (.steps bound type source limit)

theorem InputFacts.afterPremise {environment : Environment} {context : Context}
    {refinement : Refinement} {premise : Premise} {initial final : Assignment} {event : Event}
    (before : InputFacts environment context refinement initial)
    (held : PremiseHolds environment context premise initial final event) :
    InputFacts environment context
      (premiseFlow environment.language environment.provider context.rule context.spec
        context.premiseIndex context.quantifierDepth refinement premise).refinement final :=
  ⟨held.typed before.typed, held.canonical before.canonical,
    premiseFlow_holds before.represented held⟩

theorem InputFacts.afterPremises {environment : Environment} {context : Context}
    {refinement : Refinement} {premises : List Premise} {initial final : Assignment} {events : List Event}
    (before : InputFacts environment context refinement initial)
    (depth : context.quantifierDepth = 0)
    (held : PremisesHold environment context premises initial final events) :
    InputFacts environment context
      (premisesFlow environment.language environment.provider context.rule context.spec
        context.premiseIndex refinement premises).refinement final :=
  ⟨held.typed before.typed, held.canonical before.canonical,
    premisesFlow_holds depth before.represented held⟩

def GoalAdmitted.quantifiedFromRead {environment : Environment} {context : Context}
    {refinement : Refinement} {collection parameter : String} {body : Premise}
    {assignment : Assignment} {kind : CollType} {elements : List Pattern}
    (facts : InputFacts environment context refinement assignment)
    (zero : checkZeroDependencies context.spec = true)
    (supported : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement
      (.forAll collection parameter body)).supported = true)
    (stratum : context.ruleIndex ≤ environment.language.rewrites.length)
    (read : finiteCollection? context.bound.length assignment collection = some (kind, elements)) :
    GoalAdmitted environment (.quantified context parameter body 0 elements assignment) := by
  simp only [premiseFlow, Bool.and_eq_true] at supported
  split at supported <;> try simp at supported
  rename_i collectionKind elementType parameterType collectionDeclared parameterDeclared
  have same := supported.1.2.1
  subst parameterType
  obtain ⟨elementsTyped, objects⟩ := finiteCollection_elements_typed facts.typed zero collectionDeclared read
  exact .quantified refinement elementType facts zero parameterDeclared supported.1.2.2
    elementsTyped objects (finiteCollection?_canonical facts.canonical read) supported.2 stratum

theorem step_source_typed {environment : Environment} {context : Context}
    {refinement : Refinement} {source target actual : Pattern} {assignment : Assignment} {type : TypeExpr}
    (facts : InputFacts environment context refinement assignment)
    (zero : checkZeroDependencies context.spec = true)
    (supported : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement (.congruence source target)).supported = true)
    (typeFound : sourceType? environment.language context.rule source = some type)
    (projected : instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] 0 assignment source = some actual) :
    OpenPatternWellSorted environment.language environment.free context.bound type actual := by
  simp only [premiseFlow, typeFound, Bool.and_eq_true] at supported
  have schemaTyped := schemaValuesChecked_sound supported.1.1.1
  cases schemaTyped with
  | cons schemaTyped restTyped =>
    have typed := instantiateAt?_typed (locals := []) facts.typed zero supported.1.2 schemaTyped projected
    exact ⟨typed, instantiateAt?_canonical facts.canonical supported.1.1.2 supported.1.2 projected,
      instantiateAt?_objects facts.typed.2 supported.1.2 projected, typed.isWellScopedAt⟩

theorem scoped_source_typed {environment : Environment} {context : Context}
    {refinement : Refinement} {step : ScopedStepPremise} {actual : Pattern} {assignment : Assignment}
    (facts : InputFacts environment context refinement assignment)
    (zero : checkZeroDependencies context.spec = true)
    (supported : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement (.scopedStep step)).supported = true)
    (projected : instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] step.binders.length assignment step.source = some actual) :
    OpenPatternWellSorted environment.language environment.free (step.binders ++ context.bound)
      step.resultType actual := by
  simp only [premiseFlow, Bool.and_eq_true] at supported
  have schemaTyped := schemaValuesChecked_sound supported.1.1.1
  cases schemaTyped with
  | cons schemaTyped restTyped =>
    have typed := instantiateAt?_typed facts.typed zero supported.1.2 schemaTyped projected
    exact ⟨typed, instantiateAt?_canonical facts.canonical supported.1.1.2 supported.1.2 projected,
      instantiateAt?_objects facts.typed.2 supported.1.2 projected, typed.isWellScopedAt⟩

theorem GoalAdmitted.ready {environment : Environment} {goal : Execution.Goal}
    (language : checkLanguage environment = true) (admitted : GoalAdmitted environment goal) :
    Execution.checkGoalReady environment goal = true := by
  cases admitted with
  | premise _ facts zero supported _ => exact premise_ready facts.typed zero facts.represented supported
  | premises => rfl
  | @quantified context parameter body index elements assignment refinement elementType
      facts zero parameterType parameterDependencies elementsTyped elementsObjects elementsCanonical supported stratum =>
    cases elementsTyped with
    | nil => rfl
    | cons elementTyped tailTyped =>
      simp only [isObjectPatternList, Bool.and_eq_true] at elementsObjects
      exact checkTypedAssignment_complete
        (facts.typed.bindParameter parameterType parameterDependencies elementTyped elementsObjects.1)
  | @root bound type source index sourceTyped declared =>
    obtain ⟨rule, found⟩ : ∃ rule, environment.language.rewrites[index]? = some rule :=
      ⟨environment.language.rewrites[index], by simp only [List.getElem?_eq_getElem declared]⟩
    obtain ⟨spec, specified, admitted, _⟩ := checkLanguage_rule language found
    simp only [Execution.checkGoalReady, found, specified, admitted,
      checkOpenPatternWellSorted_complete sourceTyped, Bool.and_self]
  | steps => rfl

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
