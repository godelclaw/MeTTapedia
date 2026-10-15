import Mettapedia.OSLF.MeTTaIL.GeneralPremiseLocal
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Independent semantics of typed authored premises

Input query arguments are instantiated at their exact authored occurrences;
output arguments are structural scoped matches. Provider rows have declared
sorts in the complete caller context. Quantification runs in list order,
retains duplicates, restores its lexical parameter, and shares all other
outputs. A child premise denotes an actual directed authored firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open ConditionalEquationExecution (AssignmentTyped AssignmentObjects)

structure Environment where
  language : LanguageDef
  free : FreeTypeContext
  provider : ProviderSnapshot
  specifications : List (Nat × RuleBindingSpec)
  reflection : Reflection.ReflectionProfile := Reflection.ReflectionProfile.empty

/-- The plan stores declaration indices independently of declaration names. -/
def specification? (environment : Environment) (index : Nat) : Option RuleBindingSpec :=
  (environment.specifications.find? fun entry => entry.1 == index).map Prod.snd

structure Context where
  ruleIndex : Nat
  rule : RewriteRule
  spec : RuleBindingSpec
  bound : List TypeExpr
  premiseIndex : Nat
  quantifierDepth : Nat
  deriving Repr

def Context.next (context : Context) : Context :=
  { context with premiseIndex := context.premiseIndex + 1, quantifierDepth := 0 }

def Context.quantified (context : Context) : Context :=
  { context with quantifierDepth := context.quantifierDepth + 1 }

def Context.site (context : Context) (argument : Nat) : RulePatternSite :=
  .premise context.premiseIndex context.quantifierDepth argument

def TypedAssignment (environment : Environment) (context : Context)
    (assignment : Assignment) : Prop :=
  AssignmentTyped environment.language environment.free context.bound context.rule context.spec
    assignment ∧ AssignmentObjects assignment

def checkTypedAssignment (environment : Environment) (context : Context)
    (assignment : Assignment) : Bool :=
  ConditionalEquationExecution.checkAssignment environment.language environment.free context.bound
    context.rule context.spec assignment

theorem checkTypedAssignment_sound {environment : Environment} {context : Context}
    {assignment : Assignment} (checked : checkTypedAssignment environment context assignment = true) :
    TypedAssignment environment context assignment :=
  ⟨ConditionalEquationExecution.checkAssignment_sound checked,
    ConditionalEquationExecution.checkAssignment_objects checked⟩

theorem checkTypedAssignment_complete {environment : Environment} {context : Context}
    {assignment : Assignment} (typed : TypedAssignment environment context assignment) :
    checkTypedAssignment environment context assignment = true :=
  ConditionalEquationExecution.checkAssignment_complete typed.1 typed.2

inductive ArgumentHolds (context : Context) (argumentIndex : Nat) :
    RelationArgMode → Assignment → Pattern → Pattern → Assignment → Prop where
  | input {initial : Assignment} {schema value : Pattern} :
      instantiateAt? context.rule context.spec context.bound.length
        (context.site argumentIndex) [] 0 initial schema = some value →
      ArgumentHolds context argumentIndex .input initial schema value initial
  | output {initial final : Assignment} {schema value : Pattern} :
      GeneralScopedMatch.Matches context.rule context.spec context.bound.length
        (context.site argumentIndex) [] 0 initial schema value final →
      ArgumentHolds context argumentIndex .output initial schema value final

inductive ArgumentsHold (context : Context) : Nat → Assignment → List Pattern →
    List Pattern → List RelationArgMode → Assignment → Prop where
  | nil {index : Nat} {initial : Assignment} :
      ArgumentsHold context index initial [] [] [] initial
  | cons {index : Nat} {initial middle final : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {mode : RelationArgMode} {modes : List RelationArgMode} :
      ArgumentHolds context index mode initial schema value middle →
      ArgumentsHold context (index + 1) middle schemas values modes final →
      ArgumentsHold context index initial (schema :: schemas) (value :: values)
        (mode :: modes) final

theorem ArgumentHolds.extension {context : Context} {index : Nat} {mode : RelationArgMode}
    {initial final : Assignment} {schema value : Pattern}
    (held : ArgumentHolds context index mode initial schema value final) :
    Extension initial final := by
  cases held with
  | input _ => exact .refl _
  | output matching => exact matching.extends

theorem ArgumentsHold.extension {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : ArgumentsHold context index initial schemas values modes final) :
    Extension initial final := by
  induction held with
  | nil => exact .refl _
  | cons head _ inductionHypothesis => exact head.extension.trans inductionHypothesis

inductive QueryHolds (environment : Environment) (context : Context)
    (relation : String) (arguments : List Pattern) (initial : Assignment) :
    Nat → Assignment → Prop where
  | row {rowIndex : Nat} {row : ProviderRow} {signature : Signature} {final : Assignment} :
      environment.provider.rows[rowIndex]? = some row →
      signature? environment.provider relation arguments.length = some signature →
      RowTyped environment.language environment.free context.bound signature row →
      ArgumentsHold context 0 initial arguments row.values signature.modes final →
      TypedAssignment environment context final →
      QueryHolds environment context relation arguments initial rowIndex final

theorem QueryHolds.extension {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    (held : QueryHolds environment context relation arguments initial rowIndex final) :
    Extension initial final := by
  cases held with
  | row _ _ _ arguments _ => exact arguments.extension

inductive TracedArgumentsHold (context : Context) : Nat → Assignment → List Pattern →
    List Pattern → List RelationArgMode → Assignment →
      List (Nat × List GeneralScopedMatchMachine.BagChoice) → Prop where
  | nil {index : Nat} {initial : Assignment} :
      TracedArgumentsHold context index initial [] [] [] initial []
  | input {index : Nat} {initial final : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode}
      {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} :
      instantiateAt? context.rule context.spec context.bound.length
        (context.site index) [] 0 initial schema = some value →
      TracedArgumentsHold context (index + 1) initial schemas values modes final origins →
      TracedArgumentsHold context index initial (schema :: schemas) (value :: values)
        (.input :: modes) final ((index, []) :: origins)
  | output {index : Nat} {initial middle final : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode}
      {trace : List GeneralScopedMatchMachine.BagChoice}
      {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} :
      GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
        (context.site index) [] 0 initial schema value trace middle →
      TracedArgumentsHold context (index + 1) middle schemas values modes final origins →
      TracedArgumentsHold context index initial (schema :: schemas) (value :: values)
        (.output :: modes) final ((index, trace) :: origins)

theorem TracedArgumentsHold.readout {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (traced : TracedArgumentsHold context index initial schemas values modes final origins) :
    ArgumentsHold context index initial schemas values modes final := by
  induction traced with
  | nil => exact .nil
  | input interpreted _ inductionHypothesis => exact .cons (.input interpreted) inductionHypothesis
  | output matched _ inductionHypothesis => exact .cons (.output matched.matching) inductionHypothesis

inductive TracedQuery (environment : Environment) (context : Context)
    (relation : String) (arguments : List Pattern) (initial : Assignment) :
    Nat → Assignment → List (Nat × List GeneralScopedMatchMachine.BagChoice) → Prop where
  | row {rowIndex : Nat} {row : ProviderRow} {signature : Signature} {final : Assignment}
      {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} :
      environment.provider.rows[rowIndex]? = some row →
      signature? environment.provider relation arguments.length = some signature →
      RowTyped environment.language environment.free context.bound signature row →
      TracedArgumentsHold context 0 initial arguments row.values signature.modes final origins →
      TypedAssignment environment context final →
      TracedQuery environment context relation arguments initial rowIndex final origins

theorem TracedQuery.readout {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (traced : TracedQuery environment context relation arguments initial rowIndex final origins) :
    QueryHolds environment context relation arguments initial rowIndex final := by
  cases traced with
  | row selected declared typed arguments finalTyped =>
      exact .row selected declared typed arguments.readout finalTyped

/-- Runtime histories retain every provider declaration, quantified occurrence
and directed child firing. Matcher traces are retained by the query machine
alongside this semantic readout. -/
inductive Event where
  | query (premiseIndex quantifierDepth rowIndex : Nat)
      (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice))
  | freshness (premiseIndex quantifierDepth : Nat) (atom : String) (subject : Pattern)
  | quantified (premiseIndex quantifierDepth : Nat) (kind : CollType)
      (elements : List (Nat × Pattern × List Event))
  | child (premiseIndex quantifierDepth declarationIndex : Nat)
      (bound : List TypeExpr) (source target : Pattern)
      (trace targetTrace : List GeneralScopedMatchMachine.BagChoice)
      (captured completed : Assignment) (history : List Event)
  deriving Repr

mutual
inductive PremiseHolds (environment : Environment) : Context → Premise →
    Assignment → Assignment → Event → Prop where
  | query {context : Context} {relation : String} {arguments : List Pattern}
      {initial final : Assignment} {rowIndex : Nat}
      {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} :
      TracedQuery environment context relation arguments initial rowIndex final origins →
      PremiseHolds environment context (.relationQuery relation arguments) initial final
        (.query context.premiseIndex context.quantifierDepth rowIndex origins)
  | freshness {context : Context} {condition : FreshnessCondition} {initial : Assignment}
      {atom : String} {subject : Pattern} :
      freshnessSubject? context.rule context.spec context.bound context.premiseIndex
        context.quantifierDepth initial condition = some (atom, subject) →
      SyntacticallyFresh atom subject →
      PremiseHolds environment context (.freshness condition) initial initial
        (.freshness context.premiseIndex context.quantifierDepth atom subject)
  | step {context : Context} {source target actualSource actualTarget : Pattern}
      {type : TypeExpr} {initial final captured completed : Assignment}
      {childIndex : Nat} {trace targetTrace : List GeneralScopedMatchMachine.BagChoice}
      {history : List Event} :
      sourceType? environment.language context.rule source = some type →
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
        initial source = some actualSource →
      RootFiring environment context.bound type actualSource childIndex trace captured completed history
        actualTarget →
      GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
        (context.site 1) [] 0 initial target actualTarget targetTrace final →
      TypedAssignment environment context final →
      PremiseHolds environment context (.congruence source target) initial final
        (.child context.premiseIndex context.quantifierDepth childIndex context.bound
          actualSource actualTarget trace targetTrace captured completed history)
  | scopedStep {context : Context} {step : ScopedStepPremise}
      {actualSource actualTarget : Pattern} {initial final captured completed : Assignment}
      {childIndex : Nat} {trace targetTrace : List GeneralScopedMatchMachine.BagChoice}
      {history : List Event} :
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
        step.binders.length initial step.source = some actualSource →
      RootFiring environment (step.binders ++ context.bound) step.resultType actualSource
        childIndex trace captured completed history actualTarget →
      GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
        (context.site 1) [] step.binders.length initial step.target actualTarget targetTrace final →
      TypedAssignment environment context final →
      PremiseHolds environment context (.scopedStep step) initial final
        (.child context.premiseIndex context.quantifierDepth childIndex
          (step.binders ++ context.bound) actualSource actualTarget trace targetTrace captured completed history)
  | quantified {context : Context} {collection parameter : String} {body : Premise}
      {initial final : Assignment} {kind : CollType} {elements : List Pattern}
      {history : List (Nat × Pattern × List Event)} :
      finiteCollection? context.bound.length initial collection = some (kind, elements) →
      QuantifiedElements environment context parameter body 0 elements initial final history →
      PremiseHolds environment context (.forAll collection parameter body) initial final
        (.quantified context.premiseIndex context.quantifierDepth kind history)

inductive PremisesHold (environment : Environment) : Context → List Premise →
    Assignment → Assignment → List Event → Prop where
  | nil {context : Context} {initial : Assignment} :
      PremisesHold environment context [] initial initial []
  | cons {context : Context} {premise : Premise} {premises : List Premise}
      {initial middle final : Assignment} {event : Event} {events : List Event} :
      PremiseHolds environment context premise initial middle event →
      PremisesHold environment context.next premises middle final events →
      PremisesHold environment context (premise :: premises) initial final (event :: events)

inductive QuantifiedElements (environment : Environment) : Context → String → Premise → Nat →
    List Pattern → Assignment → Assignment → List (Nat × Pattern × List Event) → Prop where
  | nil {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {initial : Assignment} :
      QuantifiedElements environment context parameter body index [] initial initial []
  | cons {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {element : Pattern} {elements : List Pattern} {initial middle final : Assignment}
      {event : Event} {events : List (Nat × Pattern × List Event)} :
      TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial) →
      PremiseHolds environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) middle event →
      QuantifiedElements environment context parameter body (index + 1) elements
        (restoreParameter parameter initial middle) final events →
      QuantifiedElements environment context parameter body index (element :: elements) initial final
        ((index, element, [event]) :: events)

inductive RootFiring (environment : Environment) : List TypeExpr → TypeExpr → Pattern → Nat → List GeneralScopedMatchMachine.BagChoice →
    Assignment → Assignment → List Event → Pattern → Prop where
  | fire {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
      {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
      {captured completed : Assignment} {trace : List GeneralScopedMatchMachine.BagChoice}
      {history : List Event} :
      environment.language.rewrites[index]? = some rule →
      specification? environment index = some spec →
      admittedFor rule spec = true →
      OpenPatternWellSorted environment.language environment.free bound type source →
      GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
        rule.left source trace captured →
      TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured →
      PremisesHold environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises
        captured completed history →
      reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
        rule spec bound.length completed = some target →
      OpenPatternWellSorted environment.language environment.free bound type target →
      RootFiring environment bound type source index trace captured completed history target
end

mutual
 theorem PremiseHolds.extension {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event) :
    Extension initial final :=
  match held with
  | .query query => query.readout.extension
  | .freshness _ _ => .refl _
  | .step _ _ _ matching _ => matching.matching.extends
  | .scopedStep _ _ matching _ => matching.matching.extends
  | .quantified _ elements => elements.extension

 theorem PremisesHold.extension {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context premises initial final events) :
    Extension initial final :=
  match held with
  | .nil => .refl _
  | .cons head tail => head.extension.trans tail.extension

 theorem QuantifiedElements.extension {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    Extension initial final :=
  match held with
  | .nil => .refl _
  | .cons _ head tail =>
      (restored_extension _ _ _ _ head.extension).trans tail.extension
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
