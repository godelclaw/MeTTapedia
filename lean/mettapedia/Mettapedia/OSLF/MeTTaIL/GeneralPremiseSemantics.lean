import Mettapedia.OSLF.MeTTaIL.GeneralPremiseLocal
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Independent semantics of typed authored premises

Input query arguments are instantiated at their exact authored occurrences;
output arguments are structural scoped matches. Provider rows have declared
sorts in the complete caller context. Quantification runs in list order and
retains duplicates. Each body starts from the enclosing assignment with its
parameter rebound; body outputs remain local. A child premise denotes an
actual directed authored firing.
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
  dynamic : DynamicProvider := DynamicProvider.empty

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

/-- Resolve the native provider's inputs in the original caller assignment.
Output positions remain their authored schemas until the returned row is
processed by the ordinary structural matcher. -/
inductive DynamicInputs (context : Context) : Nat → Assignment → List Pattern →
    List RelationArgMode → List Pattern → Prop where
  | nil {index : Nat} {initial : Assignment} :
      DynamicInputs context index initial [] [] []
  | input {index : Nat} {initial : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode} :
      instantiateAt? context.rule context.spec context.bound.length
        (context.site index) [] 0 initial schema = some value →
      DynamicInputs context (index + 1) initial schemas modes values →
      DynamicInputs context index initial (schema :: schemas) (.input :: modes) (value :: values)
  | output {index : Nat} {initial : Assignment} {schema : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode} :
      DynamicInputs context (index + 1) initial schemas modes values →
      DynamicInputs context index initial (schema :: schemas) (.output :: modes) (schema :: values)

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
  | dynamicRow {nativeIndex : Nat} {signature : Signature} {final : Assignment}
      {resolved : List Pattern} {rows : List (List Pattern)} {values : List Pattern} :
      relation ∈ environment.provider.dynamicRelations →
      signature? environment.provider relation arguments.length = some signature →
      DynamicInputs context 0 initial arguments signature.modes resolved →
      environment.dynamic.Source relation resolved rows →
      rows[nativeIndex]? = some values →
      RowTyped environment.language environment.free context.bound signature ⟨relation, values⟩ →
      ArgumentsHold context 0 initial arguments values signature.modes final →
      TypedAssignment environment context final →
      QueryHolds environment context relation arguments initial
        (environment.provider.rows.length + nativeIndex) final

theorem QueryHolds.extension {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    (held : QueryHolds environment context relation arguments initial rowIndex final) :
    Extension initial final := by
  cases held with
  | row _ _ _ arguments _ => exact arguments.extension
  | dynamicRow _ _ _ _ _ _ arguments _ => exact arguments.extension

/-- The logical choices used at authored matching and input occurrences.
The retained evaluator is a realization of an interpretation, not its
semantic definition. Allocation traces remain separate from assignments. -/
structure MatchingInterpretation (Choice : Type) where
  Input : GeneralScopedMatchMachine.Request → Prop
  Matches : GeneralScopedMatchMachine.Request → List Choice → Assignment → Prop
  extension : ∀ {request trace final}, Matches request trace final →
    Extension request.initial final

/-- The established structural semantics is one interpretation of the shared
premise judgments. All source instantiation and typing operations are shared. -/
abbrev ordinaryInterpretation : MatchingInterpretation GeneralScopedMatchMachine.BagChoice where
  Input := fun request => instantiateAt? request.rule request.spec request.ambient
    request.site request.path request.depth request.initial request.schema = some request.target
  Matches := fun request trace final => GeneralScopedMatchMachine.TracedMatches
    request.rule request.spec request.ambient request.site request.path request.depth
    request.initial request.schema request.target trace final
  extension := fun matched => matched.matching.extends

/-- Runtime histories retain every provider declaration, quantified occurrence
and directed child firing. Matcher traces are retained by the query machine
alongside this semantic readout. -/
inductive Event (Choice : Type := GeneralScopedMatchMachine.BagChoice) where
  | query (premiseIndex quantifierDepth rowIndex : Nat)
      (origins : List (Nat × List Choice))
  | freshness (premiseIndex quantifierDepth : Nat) (atom : String) (subject : Pattern)
  | quantified (premiseIndex quantifierDepth : Nat) (kind : CollType)
      (elements : List (Nat × Pattern × List (Event Choice)))
  | child (premiseIndex quantifierDepth declarationIndex : Nat)
      (bound : List TypeExpr) (source target : Pattern)
      (trace targetTrace : List Choice)
      (captured completed : Assignment) (history : List (Event Choice))
  deriving Repr

namespace Interpreted

inductive TracedArgumentsHold {Choice : Type} (meaning : MatchingInterpretation Choice) (context : Context) : Nat → Assignment → List Pattern →
    List Pattern → List RelationArgMode → Assignment →
      List (Nat × List Choice) → Prop where
  | nil {index : Nat} {initial : Assignment} :
      TracedArgumentsHold meaning context index initial [] [] [] initial []
  | input {index : Nat} {initial final : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode}
      {origins : List (Nat × List Choice)} :
      meaning.Input ⟨context.rule, context.spec, context.bound.length,
        context.site index, [], 0, initial, schema, value⟩ →
      TracedArgumentsHold meaning context (index + 1) initial schemas values modes final origins →
      TracedArgumentsHold meaning context index initial (schema :: schemas) (value :: values)
        (.input :: modes) final ((index, []) :: origins)
  | output {index : Nat} {initial middle final : Assignment} {schema value : Pattern}
      {schemas values : List Pattern} {modes : List RelationArgMode}
      {trace : List Choice}
      {origins : List (Nat × List Choice)} :
      meaning.Matches ⟨context.rule, context.spec, context.bound.length,
        context.site index, [], 0, initial, schema, value⟩ trace middle →
      TracedArgumentsHold meaning context (index + 1) middle schemas values modes final origins →
      TracedArgumentsHold meaning context index initial (schema :: schemas) (value :: values)
        (.output :: modes) final ((index, trace) :: origins)

inductive TracedQuery {Choice : Type} (meaning : MatchingInterpretation Choice) (environment : Environment) (context : Context)
    (relation : String) (arguments : List Pattern) (initial : Assignment) :
    Nat → Assignment → List (Nat × List Choice) → Prop where
  | row {rowIndex : Nat} {row : ProviderRow} {signature : Signature} {final : Assignment}
      {origins : List (Nat × List Choice)} :
      environment.provider.rows[rowIndex]? = some row →
      signature? environment.provider relation arguments.length = some signature →
      RowTyped environment.language environment.free context.bound signature row →
      TracedArgumentsHold meaning context 0 initial arguments row.values signature.modes final origins →
      TypedAssignment environment context final →
      TracedQuery meaning environment context relation arguments initial rowIndex final origins
  | dynamicRow {nativeIndex : Nat} {signature : Signature} {final : Assignment}
      {resolved : List Pattern} {rows : List (List Pattern)} {values : List Pattern}
      {origins : List (Nat × List Choice)} :
      relation ∈ environment.provider.dynamicRelations →
      signature? environment.provider relation arguments.length = some signature →
      DynamicInputs context 0 initial arguments signature.modes resolved →
      environment.dynamic.Source relation resolved rows →
      rows[nativeIndex]? = some values →
      RowTyped environment.language environment.free context.bound signature ⟨relation, values⟩ →
      TracedArgumentsHold meaning context 0 initial arguments values signature.modes final origins →
      TypedAssignment environment context final →
      TracedQuery meaning environment context relation arguments initial
        (environment.provider.rows.length + nativeIndex) final origins

mutual
inductive PremiseHolds {Choice : Type} (meaning : MatchingInterpretation Choice) (environment : Environment) : Context → Premise →
    Assignment → Assignment → (Event Choice) → Prop where
  | query {context : Context} {relation : String} {arguments : List Pattern}
      {initial final : Assignment} {rowIndex : Nat}
      {origins : List (Nat × List Choice)} :
      TracedQuery meaning environment context relation arguments initial rowIndex final origins →
      PremiseHolds meaning environment context (.relationQuery relation arguments) initial final
        (.query context.premiseIndex context.quantifierDepth rowIndex origins)
  | freshness {context : Context} {condition : FreshnessCondition} {initial : Assignment}
      {atom : String} {subject : Pattern} :
      freshnessSubject? context.rule context.spec context.bound context.premiseIndex
        context.quantifierDepth initial condition = some (atom, subject) →
      SyntacticallyFresh atom subject →
      PremiseHolds meaning environment context (.freshness condition) initial initial
        (.freshness context.premiseIndex context.quantifierDepth atom subject)
  | step {context : Context} {source target actualSource actualTarget : Pattern}
      {type : TypeExpr} {initial final captured completed : Assignment}
      {childIndex : Nat} {trace targetTrace : List Choice}
      {history : List (Event Choice)} :
      sourceType? environment.language context.rule source = some type →
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
        initial source = some actualSource →
      RootFiring meaning environment context.bound type actualSource childIndex trace captured completed history
        actualTarget →
      meaning.Matches ⟨context.rule, context.spec, context.bound.length,
        context.site 1, [], 0, initial, target, actualTarget⟩ targetTrace final →
      TypedAssignment environment context final →
      PremiseHolds meaning environment context (.congruence source target) initial final
        (.child context.premiseIndex context.quantifierDepth childIndex context.bound
          actualSource actualTarget trace targetTrace captured completed history)
  | scopedStep {context : Context} {step : ScopedStepPremise}
      {actualSource actualTarget : Pattern} {initial final captured completed : Assignment}
      {childIndex : Nat} {trace targetTrace : List Choice}
      {history : List (Event Choice)} :
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
        step.binders.length initial step.source = some actualSource →
      RootFiring meaning environment (step.binders ++ context.bound) step.resultType actualSource
        childIndex trace captured completed history actualTarget →
      meaning.Matches ⟨context.rule, context.spec, context.bound.length,
        context.site 1, [], step.binders.length, initial, step.target, actualTarget⟩ targetTrace final →
      TypedAssignment environment context final →
      PremiseHolds meaning environment context (.scopedStep step) initial final
        (.child context.premiseIndex context.quantifierDepth childIndex
          (step.binders ++ context.bound) actualSource actualTarget trace targetTrace captured completed history)
  | quantified {context : Context} {collection parameter : String} {body : Premise}
      {initial final : Assignment} {kind : CollType} {elements : List Pattern}
      {history : List (Nat × Pattern × List (Event Choice))} :
      finiteCollection? context.bound.length initial collection = some (kind, elements) →
      QuantifiedElements meaning environment context parameter body 0 elements initial final history →
      PremiseHolds meaning environment context (.forAll collection parameter body) initial final
        (.quantified context.premiseIndex context.quantifierDepth kind history)

inductive PremisesHold {Choice : Type} (meaning : MatchingInterpretation Choice) (environment : Environment) : Context → List Premise →
    Assignment → Assignment → List (Event Choice) → Prop where
  | nil {context : Context} {initial : Assignment} :
      PremisesHold meaning environment context [] initial initial []
  | cons {context : Context} {premise : Premise} {premises : List Premise}
      {initial middle final : Assignment} {event : (Event Choice)} {events : List (Event Choice)} :
      PremiseHolds meaning environment context premise initial middle event →
      PremisesHold meaning environment context.next premises middle final events →
      PremisesHold meaning environment context (premise :: premises) initial final (event :: events)

/-- Each body runs in its own extension of the enclosing assignment. Its
outputs remain in that body's evidence; the next element starts from the
same enclosing assignment. -/
inductive QuantifiedElements {Choice : Type} (meaning : MatchingInterpretation Choice) (environment : Environment) : Context → String → Premise → Nat →
    List Pattern → Assignment → Assignment → List (Nat × Pattern × List (Event Choice)) → Prop where
  | nil {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {initial : Assignment} :
      QuantifiedElements meaning environment context parameter body index [] initial initial []
  | cons {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {element : Pattern} {elements : List Pattern} {initial middle final : Assignment}
      {event : (Event Choice)} {events : List (Nat × Pattern × List (Event Choice))} :
      TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial) →
      PremiseHolds meaning environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) middle event →
      QuantifiedElements meaning environment context parameter body (index + 1) elements
        initial final events →
      QuantifiedElements meaning environment context parameter body index (element :: elements) initial final
        ((index, element, [event]) :: events)

inductive RootFiring {Choice : Type} (meaning : MatchingInterpretation Choice) (environment : Environment) : List TypeExpr → TypeExpr → Pattern → Nat → List Choice →
    Assignment → Assignment → List (Event Choice) → Pattern → Prop where
  | fire {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
      {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
      {captured completed : Assignment} {trace : List Choice}
      {history : List (Event Choice)} :
      environment.language.rewrites[index]? = some rule →
      specification? environment index = some spec →
      admittedFor rule spec = true →
      OpenPatternWellSorted environment.language environment.free bound type source →
      meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
        trace captured →
      TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured →
      PremisesHold meaning environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises
        captured completed history →
      reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
        rule spec bound.length completed = some target →
      OpenPatternWellSorted environment.language environment.free bound type target →
      RootFiring meaning environment bound type source index trace captured completed history target
end

theorem QuantifiedElements.final_eq_initial {Choice : Type} {meaning : MatchingInterpretation Choice} {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List (Event Choice))}
    (held : QuantifiedElements meaning environment context parameter body index elements initial final events) :
    final = initial := by
  induction elements generalizing index initial final events with
  | nil => cases held; rfl
  | cons element elements ih =>
    cases held with
    | cons _ _ tail => exact ih tail

theorem TracedArgumentsHold.extension {Choice : Type} {meaning : MatchingInterpretation Choice}
    {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List Choice)}
    (held : TracedArgumentsHold meaning context index initial schemas values modes final origins) :
    Extension initial final := by
  induction held with
  | nil => exact .refl _
  | input _ _ ih => exact ih
  | output matched _ ih => exact (meaning.extension matched).trans ih

theorem TracedQuery.extension {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context} {relation : String}
    {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List Choice)}
    (held : TracedQuery meaning environment context relation arguments initial rowIndex final origins) :
    Extension initial final := by
  cases held with
  | row _ _ _ arguments _ => exact arguments.extension
  | dynamicRow _ _ _ _ _ _ arguments _ => exact arguments.extension

mutual
 theorem PremiseHolds.extension {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event Choice}
    (held : PremiseHolds meaning environment context premise initial final event) :
    Extension initial final :=
  match held with
  | .query query => query.extension
  | .freshness _ _ => .refl _
  | .step _ _ _ matched _ => meaning.extension matched
  | .scopedStep _ _ matched _ => meaning.extension matched
  | .quantified _ elements => elements.extension

 theorem PremisesHold.extension {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List (Event Choice)}
    (held : PremisesHold meaning environment context premises initial final events) :
    Extension initial final :=
  match held with
  | .nil => .refl _
  | .cons head tail => head.extension.trans tail.extension

 theorem QuantifiedElements.extension {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List (Event Choice))}
    (held : QuantifiedElements meaning environment context parameter body index elements initial final events) :
    Extension initial final := by
  rw [held.final_eq_initial]
  exact .refl _
end

end Interpreted

/-- The ordinary executor uses the structural specialization of the shared
judgments. It keeps the original receipt carrier and constructor payloads. -/
abbrev TracedArgumentsHold (context : Context) : Nat → Assignment → List Pattern → List Pattern → List RelationArgMode → Assignment → List (Nat × List GeneralScopedMatchMachine.BagChoice) → Prop :=
  Interpreted.TracedArgumentsHold ordinaryInterpretation context
abbrev TracedQuery (environment : Environment) (context : Context) (relation : String) (arguments : List Pattern) (initial : Assignment) : Nat → Assignment → List (Nat × List GeneralScopedMatchMachine.BagChoice) → Prop :=
  Interpreted.TracedQuery ordinaryInterpretation environment context relation arguments initial
abbrev PremiseHolds (environment : Environment) : Context → Premise → Assignment → Assignment → Event → Prop :=
  Interpreted.PremiseHolds ordinaryInterpretation environment
abbrev PremisesHold (environment : Environment) : Context → List Premise → Assignment → Assignment → List Event → Prop :=
  Interpreted.PremisesHold ordinaryInterpretation environment
abbrev QuantifiedElements (environment : Environment) : Context → String → Premise → Nat → List Pattern → Assignment → Assignment → List (Nat × Pattern × List Event) → Prop :=
  Interpreted.QuantifiedElements ordinaryInterpretation environment
abbrev RootFiring (environment : Environment) : List TypeExpr → TypeExpr → Pattern → Nat → List GeneralScopedMatchMachine.BagChoice → Assignment → Assignment → List Event → Pattern → Prop :=
  Interpreted.RootFiring ordinaryInterpretation environment

namespace TracedArgumentsHold
export Interpreted.TracedArgumentsHold (nil input output)
end TracedArgumentsHold

namespace TracedQuery
export Interpreted.TracedQuery (row dynamicRow)
end TracedQuery

namespace PremiseHolds
export Interpreted.PremiseHolds (query freshness step scopedStep quantified)
end PremiseHolds

namespace PremisesHold
export Interpreted.PremisesHold (nil cons)
end PremisesHold

namespace QuantifiedElements
export Interpreted.QuantifiedElements (nil cons)
end QuantifiedElements

namespace RootFiring
export Interpreted.RootFiring (fire)
end RootFiring

theorem Interpreted.TracedArgumentsHold.readout {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (traced : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins) :
    ArgumentsHold context index initial schemas values modes final := by
  change Interpreted.TracedArgumentsHold ordinaryInterpretation _ _ _ _ _ _ _ _ at traced
  induction traced with
  | nil => exact .nil
  | input interpreted _ inductionHypothesis => exact .cons (.input interpreted) inductionHypothesis
  | output matched _ inductionHypothesis => exact .cons (.output matched.matching) inductionHypothesis

theorem Interpreted.TracedQuery.readout {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (traced : GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins) :
    QueryHolds environment context relation arguments initial rowIndex final := by
  change Interpreted.TracedQuery ordinaryInterpretation _ _ _ _ _ _ _ _ at traced
  cases traced with
  | row selected declared typed arguments finalTyped =>
      exact .row selected declared typed arguments.readout finalTyped
  | dynamicRow registered declared resolved source selected typed arguments finalTyped =>
      exact .dynamicRow registered declared resolved source selected typed arguments.readout finalTyped

theorem QuantifiedElements.final_eq_initial {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    final = initial := Interpreted.QuantifiedElements.final_eq_initial held

theorem PremiseHolds.extension {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event) :
    Extension initial final := Interpreted.PremiseHolds.extension held

theorem PremisesHold.extension {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context premises initial final events) :
    Extension initial final := Interpreted.PremisesHold.extension held

theorem QuantifiedElements.extension {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    Extension initial final := Interpreted.QuantifiedElements.extension held

/-- A primitive interpretation map fixes the authored request and assignment.
Its trace operation is declared independently of matching and must preserve
an empty validation trace. No premise or firing simulation is a premise of
this structure. -/
structure MatchingInterpretation.Hom {Left Right : Type}
    (left : MatchingInterpretation Left) (right : MatchingInterpretation Right) where
  trace : List Left → List Right
  empty : trace [] = []
  input : ∀ {request}, left.Input request → right.Input request
  matching : ∀ {request origins final}, left.Matches request origins final →
    right.Matches request (trace origins) final

mutual
/-- Change only matcher evidence. Declaration coordinates, instantiated
objects, captures and the complete premise tree are retained. -/
def Event.mapTraces {Left Right : Type} (trace : List Left → List Right) :
    Event Left → Event Right
  | .query index depth row origins =>
      .query index depth row (origins.map fun origin => (origin.1, trace origin.2))
  | .freshness index depth atom subject => .freshness index depth atom subject
  | .quantified index depth kind elements =>
      .quantified index depth kind (Event.mapElements trace elements)
  | .child index depth declaration bound source target matched result captured completed history =>
      .child index depth declaration bound source target (trace matched) (trace result)
        captured completed (Event.mapHistory trace history)
termination_by event => sizeOf event

def Event.mapHistory {Left Right : Type} (trace : List Left → List Right) :
    List (Event Left) → List (Event Right)
  | [] => []
  | event :: events => Event.mapTraces trace event :: Event.mapHistory trace events
termination_by events => sizeOf events

def Event.mapElements {Left Right : Type} (trace : List Left → List Right) :
    List (Nat × Pattern × List (Event Left)) → List (Nat × Pattern × List (Event Right))
  | [] => []
  | (index, element, history) :: elements =>
      (index, element, Event.mapHistory trace history) :: Event.mapElements trace elements
termination_by elements => sizeOf elements
end

namespace Interpreted

theorem TracedArgumentsHold.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List Left)}
    (held : TracedArgumentsHold left context index initial schemas values modes final origins) :
    TracedArgumentsHold right context index initial schemas values modes final
      (origins.map fun origin => (origin.1, hom.trace origin.2)) := by
  induction held with
  | nil => exact .nil
  | input read _ ih =>
      simpa only [List.map_cons, hom.empty] using TracedArgumentsHold.input (hom.input read) ih
  | output matched _ ih => exact .output (hom.matching matched) ih

theorem TracedQuery.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List Left)}
    (held : TracedQuery left environment context relation arguments initial rowIndex final origins) :
    TracedQuery right environment context relation arguments initial rowIndex final
      (origins.map fun origin => (origin.1, hom.trace origin.2)) := by
  cases held with
  | row selected declared sorted arguments typed =>
      exact .row selected declared sorted (arguments.transport hom) typed
  | dynamicRow registered declared resolved source selected sorted arguments typed =>
      exact .dynamicRow registered declared resolved source selected sorted (arguments.transport hom) typed

mutual
/-- Primitive matching correspondence lifts through the entire premise AST,
including nested local quantifiers and directed child firings. -/
theorem PremiseHolds.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event Left}
    (held : PremiseHolds left environment context premise initial final event) :
    PremiseHolds right environment context premise initial final (event.mapTraces hom.trace) :=
  match held with
  | .query query => by
      simpa only [Event.mapTraces] using PremiseHolds.query (query.transport hom)
  | .freshness read fresh => by
      simpa only [Event.mapTraces] using
        (PremiseHolds.freshness (meaning := right) (environment := environment) read fresh)
  | .step typed read fired matched finalTyped => by
      simpa only [Event.mapTraces] using
        PremiseHolds.step typed read (fired.transport hom) (hom.matching matched) finalTyped
  | .scopedStep read fired matched finalTyped => by
      simpa only [Event.mapTraces] using
        PremiseHolds.scopedStep read (fired.transport hom) (hom.matching matched) finalTyped
  | .quantified read elements => by
      simpa only [Event.mapTraces] using PremiseHolds.quantified read (elements.transport hom)

theorem PremisesHold.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List (Event Left)}
    (held : PremisesHold left environment context premises initial final events) :
    PremisesHold right environment context premises initial final (Event.mapHistory hom.trace events) :=
  match held with
  | .nil => by
      simp only [Event.mapHistory]
      exact .nil
  | .cons head tail => by
      simpa only [Event.mapHistory] using PremisesHold.cons (head.transport hom) (tail.transport hom)

theorem QuantifiedElements.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List (Event Left))}
    (held : QuantifiedElements left environment context parameter body index elements initial final events) :
    QuantifiedElements right environment context parameter body index elements initial final
      (Event.mapElements hom.trace events) :=
  match held with
  | .nil => by
      simp only [Event.mapElements]
      exact .nil
  | .cons typed head tail => by
      simpa only [Event.mapElements, Event.mapHistory] using
        QuantifiedElements.cons typed (head.transport hom) (tail.transport hom)

theorem RootFiring.transport {Left Right : Type}
    {left : MatchingInterpretation Left} {right : MatchingInterpretation Right}
    (hom : left.Hom right) {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List Left} {captured completed : Assignment} {history : List (Event Left)}
    (fired : RootFiring left environment bound type source index trace captured completed history target) :
    RootFiring right environment bound type source index (hom.trace trace) captured completed
      (Event.mapHistory hom.trace history) target :=
  match fired with
  | .fire declared specified admitted sorted matched typed premises reduced targetTyped =>
      .fire declared specified admitted sorted (hom.matching matched) typed
        (premises.transport hom) reduced targetTyped
end

end Interpreted

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
