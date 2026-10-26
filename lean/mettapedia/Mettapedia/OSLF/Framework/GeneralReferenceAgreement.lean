import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticContracts
import Mettapedia.OSLF.Framework.GeneralCanonicalCongruenceAgreement
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# The general typed semantics is the reference relation on first-order profiles

Three agreements compose:
- on a first-order profile the general typed semantics relates the same well-sorted terms as the
  canonical relation (`FirstOrderProfile.general_step_iff_canonical`);
- without equations the canonical relation is the least contextual one
  (`langSemanticReducesUsing_iff_langReducesUsing_of_equation_free`);
- on an aligned language the least contextual relation is the reference relation
  (`ReferenceStep.contextualStep_iff_step`).

The directed forward bridge also supports recursively binder-free collection schemas, while its
reverse typing reconstruction remains restricted to the proved first-order profile.

So on a first-order profile whose rules are aligned, the general typed semantics is the reference
relation (`FirstOrderProfile.general_step_iff_reference`). With equations, the canonical operational
theory of a language (`langGSLTUsing`) is the reference relation modulo equations when the rules and
equations are aligned (`langGSLT_step_iff_stepModulo`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

/-- **On an aligned first-order profile the general typed semantics is the reference relation.** -/
theorem FirstOrderProfile.general_step_iff_reference (profile : FirstOrderProfile language provider)
    (aligned : ReferenceStep.ReferenceProfile language)
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv provider) (bound : List TypeExpr) (type : TypeExpr)
    {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language provider).snapshot.language
      (rootPlan language provider).snapshot.free bound type source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan language provider) bound type).Step source target ↔
      ReferenceStep.Step relEnv language source target :=
  (profile.general_step_iff_canonical relEnv reads bound type typed).trans
    ((TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free relEnv profile.equationFree
      source target).trans (ReferenceStep.contextualStep_iff_step relEnv language aligned))

/-- **The canonical operational theory is the reference relation modulo equations**, when the rules and
the equations are aligned. -/
theorem langGSLT_step_iff_stepModulo (relEnv : Engine.RelationEnv) (aligned : ReferenceStep.ReferenceProfile language)
    (equations : ReferenceStep.EquationsAligned language) {source target : Pattern} :
    (TypeSynthesis.langGSLTUsing relEnv language).Step source target ↔
      ReferenceStep.StepModulo relEnv language source target :=
  ReferenceStep.stepModuloEquations_iff aligned equations

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec MeTTaIL.RuleBinding
open MeTTaIL.ScopedRuleMatching MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace QuantifiedReference

/-- Ordinary projection preserves the complete local parameter operation,
including removal of every shadowed entry. -/
theorem ordinary_removeParameter (assignment : Assignment) (parameter : String) :
    ordinary (GeneralPremise.removeParameter parameter assignment) =
      (ordinary assignment).filter (fun entry => entry.1 != parameter) := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key,value⟩ := entry
      unfold ordinary at ih
      by_cases same : key = parameter
      · subst key
        simp [GeneralPremise.removeParameter, ordinary, ih]
      · simp [GeneralPremise.removeParameter, ordinary, same, ih]

theorem ordinary_bindParameter (assignment : Assignment) (parameter : String)
    (bound : List TypeExpr) (element : Pattern) :
    ordinary (GeneralPremise.bindParameter parameter (GeneralPremise.localValue bound element) assignment) =
      ReferenceStep.bindParameter (ordinary assignment) parameter element := by
  simp only [GeneralPremise.bindParameter, ordinary, List.map_cons, GeneralPremise.localValue,
    ReferenceStep.bindParameter]
  exact congrArg (List.cons (parameter,element)) (ordinary_removeParameter assignment parameter)

/-- Finite-carrier extraction reads the exact ordinary body of each
dependency-free contextual value. It neither sorts nor contracts the list. -/
theorem finiteCollection_readout {ambient : Nat} {assignment : Assignment}
    (roots : GeneralPremise.RootValues ambient assignment) (collection : String) :
    GeneralPremise.finiteCollection? ambient assignment collection =
      ((ordinary assignment).lookup collection).bind GeneralPremise.concreteCollection? := by
  unfold GeneralPremise.finiteCollection?
  rw [ordinary_lookup]
  cases found : lookup assignment collection with
  | none => rfl
  | some value =>
      simp only [Option.bind_eq_bind, Option.map_some, Option.bind_some, root_value_readout (roots collection value found)]

theorem finiteCollection_lookup {ambient : Nat} {assignment : Assignment} {collection : String}
    {kind : CollType} {elements : List Pattern}
    (roots : GeneralPremise.RootValues ambient assignment)
    (read : GeneralPremise.finiteCollection? ambient assignment collection = some (kind,elements)) :
    (ordinary assignment).lookup collection = some (.collection kind elements none) := by
  rw [finiteCollection_readout roots] at read
  cases found : (ordinary assignment).lookup collection with
  | none => simp [found] at read
  | some value =>
      simp only [found,Option.bind_some] at read
      cases value with
      | collection actualKind actualElements rest =>
          cases rest with
          | none =>
              cases Option.some.inj read
              rfl
          | some _ => cases read
      | _ => cases read

theorem removeParameter_unique {assignment : Assignment} {parameter : String}
    (unique : (assignment.map Prod.fst).Nodup) :
    ((GeneralPremise.removeParameter parameter assignment).map Prod.fst).Nodup := by
  rw [← ordinary_names, ordinary_removeParameter]
  have projected : ((ordinary assignment).map Prod.fst).Nodup := by
    simpa only [ordinary_names] using unique
  exact projected.sublist (List.filter_sublist.map Prod.fst)

theorem bindParameter_unique {assignment : Assignment} {parameter : String}
    {value : ContextualValue} (unique : (assignment.map Prod.fst).Nodup) :
    ((GeneralPremise.bindParameter parameter value assignment).map Prod.fst).Nodup := by
  simp only [GeneralPremise.bindParameter,List.map_cons]
  exact List.nodup_cons.mpr ⟨
    (scoped_lookup_none_iff_not_mem_names _ parameter).mp
      (GeneralPremise.lookup_remove_parameter assignment parameter),
    removeParameter_unique unique⟩

theorem ordinary_lookup_member {assignment : Assignment} {key : String} {value : ContextualValue}
    (unique : (assignment.map Prod.fst).Nodup) (member : (key,value) ∈ assignment) :
    lookup assignment key = some value := by
  induction assignment with
  | nil => cases member
  | cons entry rest ih =>
      obtain ⟨first,stored⟩ := entry
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | later
      · cases same
        simp
      · have different : first ≠ key := by
          intro same
          exact parts.1 (List.mem_map.mpr ⟨(key,value),later,same.symm⟩)
        simp only [GeneralPremise.lookup_cons,beq_eq_false_iff_ne.mpr different,
          Bool.false_eq_true,if_false]
        exact ih parts.2 later

theorem ordinary_compatible_extension {initial final : Assignment}
    (unique : (initial.map Prod.fst).Nodup) (preserved : GeneralPremise.Extension initial final) :
    Compatible (ordinary final) (ordinary initial) := by
  intro entry member
  obtain ⟨⟨key,value⟩,stored,rfl⟩ := List.mem_map.mp member
  rw [ordinary_lookup,preserved key value (ordinary_lookup_member unique stored)]
  rfl

/-- Typed contextual captures with canonical metadata project to actual
ordinary typed bindings. Object syntax and metadata are distinct premises. -/
theorem ordinary_capturesTyped {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {assignment : Assignment} (typed : GeneralPremise.TypedAssignment environment context assignment)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (unique : (assignment.map Prod.fst).Nodup) :
    CapturesTyped environment.language environment.free context.bound context.rule.typeContext
      (ordinary assignment) := by
  intro entry member
  obtain ⟨⟨key,value⟩,stored,rfl⟩ := List.mem_map.mp member
  obtain ⟨dependencies,expected,declared,sorted,_,_,bodyTyped⟩ := typed.1 key value stored
  have empty := GeneralPremise.checkZeroDependencies_sound context.spec zero key dependencies declared
  rw [empty,List.nil_append] at bodyTyped
  exact ⟨expected,sorted,bodyTyped,canonical key value (ordinary_lookup_member unique stored),
    typed.2 key value stored,bodyTyped.isWellScopedAt⟩

theorem ordinary_scopedCompatible {ambient : Nat} {assignment : Assignment}
    (roots : GeneralPremise.RootValues ambient assignment)
    (unique : (assignment.map Prod.fst).Nodup) :
    ScopedCompatible ambient (ordinary assignment) assignment := by
  rintro ⟨key,value⟩ member
  have found := ordinary_lookup_member unique member
  obtain ⟨dependencies,caller,_⟩ := roots key value found
  exact ⟨dependencies,caller,by rw [ordinary_lookup,found]; rfl⟩

/-- The current premise is read from the actual rule at its retained
quantifier depth. -/
def Located (context : GeneralPremise.Context) (premise : Premise) : Prop :=
  (context.rule.premises[context.premiseIndex]?).bind (quantifiedBody? context.quantifierDepth) = some premise

theorem quantifiedBody_next (depth : Nat) (premise : Premise) :
    quantifiedBody? (depth + 1) premise =
      (quantifiedBody? depth premise).bind (fun current => match current with
        | .forAll _ _ body => some body
        | _ => none) := by
  induction depth generalizing premise with
  | zero => cases premise <;> rfl
  | succ depth ih =>
      cases premise with
      | forAll collection parameter body => exact ih body
      | _ => rfl

theorem Located.quantified {context : GeneralPremise.Context} {collection parameter : String} {body : Premise}
    (located : Located context (.forAll collection parameter body)) : Located context.quantified body := by
  unfold Located at located ⊢
  obtain ⟨premise,selected,nested⟩ := Option.bind_eq_some_iff.mp located
  simp only [GeneralPremise.Context.quantified,selected,Option.bind_some,
    quantifiedBody_next,nested]

theorem Located.query {context : GeneralPremise.Context} {relation : String} {arguments : List Pattern}
    (located : Located context (.relationQuery relation arguments)) {position : Nat} {schema : Pattern}
    (selected : arguments[position]? = some schema) :
    sitePattern? context.rule (context.site position) = some schema := by
  obtain ⟨premise,declared,nested⟩ := Option.bind_eq_some_iff.mp located
  simp only [GeneralPremise.Context.site,sitePattern?,declared,Option.bind_eq_bind,Option.bind_some,nested]
  exact selected

theorem tracedArguments_defined {context : GeneralPremise.Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins) :
    Defined (ordinary final) (schemas.flatMap Pattern.freeFvarNames) := by
  induction held with
  | nil => intro _ member; cases member
  | input read tail ih =>
      have bound := instantiation_bound (shapes _ (List.mem_cons_self ..)) read
      intro key member
      simp only [List.flatMap_cons,List.mem_append] at member
      rcases member with here | later
      · obtain ⟨value,found⟩ := bound key here
        exact ⟨value.body,by rw [ordinary_lookup,tail.readout.extension key value found]; rfl⟩
      · exact ih (fun child member => shapes child (List.mem_cons_of_mem _ member)) key later
  | output matched tail ih =>
      intro key member
      simp only [List.flatMap_cons,List.mem_append] at member
      rcases member with here | later
      · obtain ⟨value,found⟩ := GeneralPremise.matching_bound_names matched.matching key here
        exact ⟨value.body,by rw [ordinary_lookup,tail.readout.extension key value found]; rfl⟩
      · exact ih (fun child member => shapes child (List.mem_cons_of_mem _ member)) key later

/-- Literal reference queries reconstruct typed ordinary query derivations
at their actual quantifier depth. Input availability, schema sorts and row
typing are independent primitive eligibility facts. -/
theorem query_fromReference {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {relation : String} {arguments : List Pattern} {initial : Assignment}
    {current result : Bindings} {signature : GeneralPremise.Signature}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (distinct : relation ≠ "eq")
    (signatureFound : GeneralPremise.signature? environment.provider relation arguments.length = some signature)
    (locations : ∀ position schema, arguments[position]? = some schema →
      sitePattern? context.rule (context.site position) = some schema)
    (shapes : ∀ argument ∈ arguments, FirstOrder argument)
    (schemasTyped : List.Forall₂ (HasType environment.language (FreeTypeContext.ofList context.rule.typeContext) [])
      arguments signature.argumentTypes)
    (inputs : GeneralPremise.BoundNames initial (GeneralPremise.queryInputNames arguments signature.modes))
    (currentTyped : CapturesTyped environment.language environment.free context.bound context.rule.typeContext current)
    (compatible : ScopedCompatible context.bound.length current initial)
    (member : result ∈ Engine.premiseStepWithEnv relEnv environment.language current
      (.relationQuery relation arguments)) :
    ∃ final rowIndex origins,
      GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins ∧
      ScopedCompatible context.bound.length result final ∧
      CapturesTyped environment.language environment.free context.bound context.rule.typeContext result := by
  obtain ⟨tuple,extension,provided,matched,merged⟩ :=
    ConditionalEquationExecution.relationQueryStep_readout relEnv environment.language current result
      relation arguments member
  rw [builtinRelationTuples_eq_nil distinct,List.nil_append] at provided
  obtain ⟨signatureMember,signatureRelation,_,modesLength⟩ :=
    GeneralPremise.signature?_readout _ _ _ _ signatureFound
  rw [← signatureRelation] at provided
  obtain ⟨row,rowMember,rowRelation,rowValues⟩ := (reads signature signatureMember _ _).mp provided
  subst rowValues
  obtain ⟨readback,resultDefined⟩ := relationArgs_sound shapes matched
    (fun _ _ found => mergeBindings_subsumed_left merged found)
    (fun _ _ found => mergeBindings_subsumed_right merged found)
  obtain ⟨closedSignature,closedFound,closedTyped⟩ :=
    GeneralPremise.checkProviderClosed_row _ _ _ providerClosed row rowMember
  have sameSignature : closedSignature = signature := by
    rw [rowRelation,signatureRelation,← readback,List.length_map,signatureFound] at closedFound
    exact (Option.some.inj closedFound).symm
  subst closedSignature
  have rowTyped := GeneralPremise.closed_row_in_bound closedTyped context.bound
  have extensionTyped := relationArgs_typed valid shapes matched schemasTyped rowTyped.2
  have resultTyped := capturesTyped_merge currentTyped extensionTyped merged
  have lifted : ScopedCompatible context.bound.length result initial :=
    compatible_lift compatible (fun _ _ found => merge_lookup_left merged found)
  obtain ⟨final,origins,traced,finalCompatible,_,_⟩ := tracedArguments_construct_at
    (ruleIndex := context.ruleIndex) (premiseIndex := context.premiseIndex)
    (quantifierDepth := context.quantifierDepth) contextUnique locations resultTyped
    arguments signature.modes 0 (fun _ _ selected => by simpa using selected) shapes modesLength.symm
    resultDefined inputs lifted
  rw [readback,← specification] at traced
  change GeneralPremise.TracedArgumentsHold context 0 initial arguments row.values signature.modes final origins
    at traced
  obtain ⟨rowIndex,selected⟩ := List.mem_iff_getElem?.mp rowMember
  have finalTyped : GeneralPremise.TypedAssignment environment context final := by
    unfold GeneralPremise.TypedAssignment
    rw [specification]
    exact finalCompatible.typed resultTyped contextUnique
  exact ⟨final,rowIndex,origins,.row selected signatureFound rowTyped traced finalTyped,finalCompatible,resultTyped⟩

/-- Recursive validation syntax indexed by its schema domain. This is a
syntactic theorem domain; it grants no execution or source-policy admission. -/
inductive ValidationWith (Schema : Pattern → Prop) : Premise → Prop where
  | query {relation : String} {arguments : List Pattern}
      (distinct : relation ≠ "eq")
      (shapes : ∀ argument ∈ arguments, Schema argument) :
      ValidationWith Schema (.relationQuery relation arguments)
  | freshness {condition : FreshnessCondition} (shape : Schema condition.term) :
      ValidationWith Schema (.freshness condition)
  | quantified {collection parameter : String} {body : Premise} (bodyShape : ValidationWith Schema body) :
      ValidationWith Schema (.forAll collection parameter body)

abbrev Validation := ValidationWith FirstOrder

/-- The conservative literal-input theorem domain follows actual provider
modes, including queries beneath local finite quantifiers. Recursive output
schemas are not restricted by this predicate. -/
def FirstOrderQueryInputs (provider : GeneralPremise.ProviderSnapshot) : Premise → Prop
  | .relationQuery relation arguments =>
      ∀ signature,GeneralPremise.signature? provider relation arguments.length = some signature →
        ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
          signature.modes[position]? = some RelationArgMode.input → FirstOrder schema
  | .forAll _ _ body => FirstOrderQueryInputs provider body
  | _ => True

theorem Validation.firstOrderQueryInputs {provider : GeneralPremise.ProviderSnapshot}
    {premise : Premise} (shape : Validation premise) : FirstOrderQueryInputs provider premise := by
  induction shape with
  | query _ schemas =>
      intro signature _ position schema selected _
      exact schemas schema (List.mem_of_getElem? selected)
  | freshness _ => trivial
  | quantified _ ih => exact ih

#print axioms Validation.firstOrderQueryInputs

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

/-- A typed scoped freshness witness supplies the actual literal reference
base premise, at any quantifier depth. -/
theorem freshness_toReference {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {condition : FreshnessCondition} {initial : Assignment} {atom : String} {subject : Pattern}
    (relEnv : Engine.RelationEnv)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (shape : FirstOrder condition.term)
    (roots : GeneralPremise.RootValues context.bound.length initial)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound
      context.premiseIndex context.quantifierDepth initial condition = some (atom,subject))
    (fresh : GeneralPremise.SyntacticallyFresh atom subject) :
    ordinary initial ∈ Engine.premiseStepWithEnv relEnv environment.language
      (ordinary initial) (.freshness condition) := by
  unfold GeneralPremise.freshnessSubject? at read
  cases named : GeneralPremise.freshnessName? context.bound.length initial condition.varName with
  | none => simp [named] at read
  | some actualAtom =>
      cases instantiated : instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial condition.term with
      | none => simp [named,instantiated] at read
      | some actualSubject =>
          have same : (actualAtom,actualSubject) = (atom,subject) := by
            simpa only [named,instantiated,Option.bind_eq_bind,Option.bind_some,Option.some.injEq] using read
          cases same
          have namedRaw : resolveFreshVarName (ordinary initial) condition.varName = some atom := by
            rw [← freshnessName_eq_resolve roots]
            exact named
          have subjectRaw : applyBindings (ordinary initial) condition.term = subject := by
            rw [specification] at instantiated
            exact instantiation_readout shape roots instantiated
          simp only [Engine.premiseStepWithEnv,namedRaw,subjectRaw]
          rw [if_pos (show Substitution.checkFreshness ⟨atom,subject⟩ = true from
            (GeneralPremise.syntactic_freshness_iff _ _).mpr fresh)]
          exact List.mem_singleton_self _


/-- A successful typed scoped freshness read has exactly the name and
subject used by the original literal reference evaluator. -/
theorem freshness_readout_recursive {context : GeneralPremise.Context} {condition : FreshnessCondition}
    {initial : Assignment} {atom : String} {subject : Pattern}
    (shape : binderFree condition.term = true)
    (roots : GeneralPremise.RootValues context.bound.length initial)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound
      context.premiseIndex context.quantifierDepth initial condition = some (atom,subject)) :
    resolveFreshVarName (ordinary initial) condition.varName = some atom ∧
      applyBindings (ordinary initial) condition.term = subject := by
  unfold GeneralPremise.freshnessSubject? at read
  cases named : GeneralPremise.freshnessName? context.bound.length initial condition.varName with
  | none => simp [named] at read
  | some actualAtom =>
      cases instantiated : instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial condition.term with
      | none => simp [named,instantiated] at read
      | some actualSubject =>
          have same : (actualAtom,actualSubject) = (atom,subject) := by
            simpa only [named,instantiated,Option.bind_eq_bind,Option.bind_some,Option.some.injEq] using read
          cases same
          constructor
          · rw [← freshnessName_eq_resolve roots]
            exact named
          · exact binderFree_instantiation_readout shape roots instantiated

theorem freshness_readout {context : GeneralPremise.Context} {condition : FreshnessCondition}
    {initial : Assignment} {atom : String} {subject : Pattern}
    (_specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (shape : FirstOrder condition.term)
    (roots : GeneralPremise.RootValues context.bound.length initial)
    (read : GeneralPremise.freshnessSubject? context.rule context.spec context.bound
      context.premiseIndex context.quantifierDepth initial condition = some (atom,subject)) :
    resolveFreshVarName (ordinary initial) condition.varName = some atom ∧
      applyBindings (ordinary initial) condition.term = subject := by
  exact freshness_readout_recursive shape.binderFree roots read


#print axioms ordinary_removeParameter
#print axioms ordinary_bindParameter
#print axioms finiteCollection_readout
#print axioms finiteCollection_lookup
#print axioms removeParameter_unique
#print axioms bindParameter_unique
#print axioms ordinary_lookup_member
#print axioms ordinary_compatible_extension
#print axioms ordinary_capturesTyped
#print axioms ordinary_scopedCompatible
#print axioms quantifiedBody_next
#print axioms Located.quantified
#print axioms Located.query
#print axioms tracedArguments_defined
#print axioms query_fromReference
#print axioms freshness_toReference
#print axioms freshness_readout

end QuantifiedReference
end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.QuantifiedReference

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec MeTTaIL.RuleBinding
open MeTTaIL.ScopedRuleMatching MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Exact lookup readback determines the complete bound-name account;
the two stores keep their original layouts. -/
theorem bindingAgreement_of_lookups {names : List String} {assignment : Assignment} {bindings : Bindings}
    (scopedUnique : (assignment.map Prod.fst).Nodup) (rawUnique : (bindings.map Prod.fst).Nodup)
    (rawNames : SameNames bindings names)
    (lookups : ∀ name,(lookup assignment name).map ContextualValue.body = bindings.lookup name) :
    BindingAgreement names assignment bindings := by
  refine ⟨scopedUnique,rawUnique,?_,rawNames,lookups⟩
  intro name
  have corresponding : name ∈ (ordinary assignment).map Prod.fst ↔ name ∈ bindings.map Prod.fst := by
    rw [← lookup_some_iff_mem_names (ordinary assignment) name,← lookup_some_iff_mem_names bindings name]
    simp only [ordinary_lookup,lookups name]
  simpa only [ordinary_names] using corresponding.trans (rawNames name)

theorem bindingAgreement_of_scopedCompatible {ambient : Nat} {names : List String}
    {assignment : Assignment} {bindings : Bindings}
    (compatible : ScopedCompatible ambient bindings assignment)
    (scopedUnique : (assignment.map Prod.fst).Nodup) (rawUnique : (bindings.map Prod.fst).Nodup)
    (bound : GeneralPremise.BoundNames assignment names)
    (rawNames : ∀ name ∈ bindings.map Prod.fst,name ∈ names) :
    BindingAgreement names assignment bindings := by
  have fullNames : SameNames bindings names := by
    intro name
    constructor
    · exact rawNames name
    · intro member
      obtain ⟨value,found⟩ := bound name member
      have rawFound := (compatible (name,value)
        (ConditionalEquationExecution.lookup_assignment_member assignment name value found)).2.2
      exact (lookup_some_iff_mem_names bindings name).mp ⟨value.body,rawFound⟩
  apply bindingAgreement_of_lookups scopedUnique rawUnique fullNames
  intro name
  cases found : lookup assignment name with
  | some value =>
      have read := (compatible (name,value)
        (ConditionalEquationExecution.lookup_assignment_member assignment name value found)).2.2
      rw [read]
      rfl
  | none =>
      have absent : bindings.lookup name = none := by
        apply (lookup_none_iff_not_mem_names bindings name).mpr
        intro member
        obtain ⟨value,present⟩ := bound name ((fullNames name).mp member)
        rw [found] at present
        cases present
      rw [absent]
      rfl

theorem bindingAgreement_available {names : List String} {assignment : Assignment} {bindings : Bindings}
    (agreement : BindingAgreement names assignment bindings) : GeneralPremise.BoundNames assignment names := by
  intro name member
  have inScope := (agreement.scopedNames name).mpr member
  have ordinaryPresent : name ∈ (ordinary assignment).map Prod.fst := by
    simpa only [ordinary_names] using inScope
  obtain ⟨body,read⟩ := (lookup_some_iff_mem_names (ordinary assignment) name).mpr ordinaryPresent
  rw [ordinary_lookup] at read
  obtain ⟨value,found,_⟩ := Option.map_eq_some_iff.mp read
  exact ⟨value,found⟩

theorem raw_bindParameter_unique {bindings : Bindings} (parameter : String) (element : Pattern)
    (unique : (bindings.map Prod.fst).Nodup) :
    ((ReferenceStep.bindParameter bindings parameter element).map Prod.fst).Nodup := by
  unfold ReferenceStep.bindParameter
  simp only [List.map_cons]
  refine List.nodup_cons.mpr ⟨?_,unique.sublist (List.filter_sublist.map Prod.fst)⟩
  intro member
  obtain ⟨entry,stored,key⟩ := List.mem_map.mp member
  have different := (List.mem_filter.mp stored).2
  simp only [key,bne_self_eq_false,Bool.false_eq_true] at different

theorem raw_bindParameter_names (bindings : Bindings) (parameter : String) (element : Pattern) (name : String) :
    name ∈ (ReferenceStep.bindParameter bindings parameter element).map Prod.fst ↔
      name = parameter ∨ name ∈ bindings.map Prod.fst := by
  unfold ReferenceStep.bindParameter
  simp only [List.map_cons,List.mem_cons]
  constructor
  · rintro (rfl | member)
    · exact Or.inl rfl
    · obtain ⟨entry,stored,key⟩ := List.mem_map.mp member
      exact Or.inr (List.mem_map.mpr ⟨entry,(List.mem_filter.mp stored).1,key⟩)
  · rintro (rfl | member)
    · exact Or.inl rfl
    · by_cases same : name = parameter
      · exact Or.inl same
      · right
        obtain ⟨entry,stored,key⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨entry,List.mem_filter.mpr ⟨stored,by simp [key,same]⟩,key⟩

theorem raw_bindParameter_lookup (bindings : Bindings) (parameter : String) (element : Pattern) (name : String) :
    (ReferenceStep.bindParameter bindings parameter element).lookup name =
      if parameter == name then some element else bindings.lookup name := by
  by_cases same : parameter = name
  · subst parameter
    simp [ReferenceStep.bindParameter,Bindings.lookup]
  · simp only [ReferenceStep.bindParameter,Bindings.lookup,List.find?_cons,
      beq_eq_false_iff_ne.mpr same,Bool.false_eq_true,if_false]
    have filtered : (bindings.filter (fun entry => entry.1 != parameter)).find?
        (fun entry => entry.1 == name) = bindings.find? (fun entry => entry.1 == name) := by
      induction bindings with
      | nil => rfl
      | cons entry tail ih =>
          by_cases removed : entry.1 = parameter
          · simp only [List.filter_cons,removed,bne_self_eq_false,Bool.false_eq_true,if_false,
              List.find?_cons,beq_eq_false_iff_ne.mpr same]
            exact ih
          · simp only [List.filter_cons,show (entry.1 != parameter) = true by simp [removed],
              ↓reduceIte,List.find?_cons]
            split <;> first | rfl | exact ih
    rw [filtered]

/-- Local parameter shadowing transports exact binding readback, including
all absent names and both unique-key stores. -/
theorem bindingAgreement_bindParameter {names : List String} {assignment : Assignment} {bindings : Bindings}
    (agreement : BindingAgreement names assignment bindings) (parameter : String)
    (bound : List TypeExpr) (element : Pattern) :
    BindingAgreement (parameter::names)
      (GeneralPremise.bindParameter parameter (GeneralPremise.localValue bound element) assignment)
      (ReferenceStep.bindParameter bindings parameter element) := by
  apply bindingAgreement_of_lookups (bindParameter_unique agreement.scopedUnique)
    (raw_bindParameter_unique parameter element agreement.ordinaryUnique)
  · intro name
    rw [raw_bindParameter_names,agreement.ordinaryNames name]
    simp only [List.mem_cons]
  · intro name
    rw [raw_bindParameter_lookup]
    by_cases same : name = parameter
    · subst name
      simp only [GeneralPremise.lookup_bind_parameter,Option.map_some,GeneralPremise.localValue,
        beq_self_eq_true,if_true]
    · rw [GeneralPremise.lookup_bind_other _ _ _ _ same,
        show (parameter == name) = false by simp [Ne.symm same]]
      exact agreement.lookups name

theorem bindingAgreement_compatible_later {names : List String} {initial final : Assignment}
    {bindings : Bindings} (agreement : BindingAgreement names initial bindings)
    (preserved : GeneralPremise.Extension initial final) : Compatible (ordinary final) bindings := by
  intro entry member
  have rawFound := bindings_lookup_of_mem agreement.ordinaryUnique member
  have read := (agreement.lookups entry.1).trans rawFound
  obtain ⟨value,found,body⟩ := Option.map_eq_some_iff.mp read
  rw [ordinary_lookup,preserved entry.1 value found,Option.map_some,body]

/-- First-order output matching preserves unique keys and adds exactly the
declared output names; input positions introduce no bindings. -/
theorem arguments_binding_names {context : GeneralPremise.Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    (shapes : ∀ schema ∈ schemas,FirstOrder schema)
    (held : GeneralPremise.ArgumentsHold context index initial schemas values modes final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧ ∀ name,name ∈ final.map Prod.fst ↔
      name ∈ initial.map Prod.fst ∨ name ∈ GeneralPremise.queryOutputNames schemas modes := by
  induction held with
  | nil => exact ⟨unique,by intro name; simp [GeneralPremise.queryOutputNames]⟩
  | @cons index initial middle final schema value schemas values mode modes head tail ih =>
      have restShapes := fun child member => shapes child (List.mem_cons_of_mem _ member)
      cases head with
      | input _ =>
          simpa only [queryOutputNames_input] using ih restShapes unique
      | output matched =>
          obtain ⟨middleUnique,middleNames⟩ := matching_unique_names
            (shapes schema (List.mem_cons_self ..)) matched unique
          obtain ⟨finalUnique,finalNames⟩ := ih restShapes middleUnique
          refine ⟨finalUnique,?_⟩
          intro name
          rw [finalNames name,middleNames name,queryOutputNames_output,List.mem_append]
          exact or_assoc

theorem arguments_binding_names_recursive {context : GeneralPremise.Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : GeneralPremise.ArgumentsHold context index initial schemas values modes final)
    (unique : (initial.map Prod.fst).Nodup) :
    (final.map Prod.fst).Nodup ∧ ∀ name,name ∈ final.map Prod.fst ↔
      name ∈ initial.map Prod.fst ∨ name ∈ GeneralPremise.queryOutputNames schemas modes := by
  induction held with
  | nil => exact ⟨unique,by intro name; simp [GeneralPremise.queryOutputNames]⟩
  | @cons index initial middle final schema value schemas values mode modes head tail ih =>
      cases head with
      | input _ =>
          simpa only [queryOutputNames_input] using ih unique
      | output matched =>
          obtain ⟨middleUnique,middleNames⟩ := matching_unique_names_recursive matched unique
          obtain ⟨finalUnique,finalNames⟩ := ih middleUnique
          refine ⟨finalUnique,?_⟩
          intro name
          rw [finalNames name,middleNames name,queryOutputNames_output,List.mem_append]
          exact or_assoc

/-- A real typed provider derivation earns a literal reference query while
retaining the full completed binding readback, not just its existence. -/
theorem query_toReference_bindings_recursive {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    {available : List String} {bindings : Bindings}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (noDynamic : environment.provider.dynamicRelations = [])
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (shapes : binderFreeList arguments = true)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec available (.relationQuery relation arguments)).supported = true)
    (held : GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins) :
    ∃ result,result ∈ Engine.premiseStepWithEnv relEnv environment.language bindings
      (.relationQuery relation arguments) ∧ BindingAgreement
        (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
          available (.relationQuery relation arguments)).available final result := by
  cases held with
  | @row rowIndex row signature final origins selected declared rowTyped argumentsHeld finalTyped =>
      simp only [GeneralPremise.premiseFlow,declared,Bool.and_eq_true] at supported ⊢
      have roots := finalTyped.rootValues zero
      have compatible := bindingAgreement_compatible_later agreement argumentsHeld.readout.extension
      obtain ⟨extension,matched,extensionCompatible,_,extensionNames,covers⟩ :=
        tracedArguments_relation roots argumentsHeld shapes (.refl _) compatible agreement.ordinaryUnique
      obtain ⟨result,merged,resultCompatible,resultUnique,resultNames⟩ :=
        merge_compatible (ordinary final) bindings extension compatible extensionCompatible agreement.ordinaryUnique
      obtain ⟨signatureMember,signatureRelation,_,modesLength⟩ :=
        GeneralPremise.signature?_readout _ _ _ _ declared
      have lengths := modesLength.symm
      have rawNames : SameNames result
          (GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups := by
        intro name
        rw [resultNames name,agreement.ordinaryNames name,List.mem_eraseDups,List.mem_append]
        constructor
        · rintro (earlier | output)
          · exact Or.inr earlier
          · obtain ⟨entry,member,rfl⟩ := List.mem_map.mp output
            rcases query_names_cover lengths _ (extensionNames entry member) with input | produced
            · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ supported.1 _ input)
            · exact Or.inl produced
        · rintro (produced | earlier)
          · rcases covers name (queryOutputNames_subset produced) with prior | captured
            · exact Or.inl ((agreement.ordinaryNames name).mp prior)
            · exact Or.inr captured
          · exact Or.inl earlier
      obtain ⟨scopedUnique,scopedNames⟩ := arguments_binding_names_recursive argumentsHeld.readout agreement.scopedUnique
      have finalNames : ∀ name,name ∈ final.map Prod.fst ↔
          name ∈ (GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups := by
        intro name
        rw [scopedNames name,agreement.scopedNames name,List.mem_eraseDups,List.mem_append]
        exact or_comm
      have rawDomain : SameNames result ((ordinary final).map Prod.fst) := by
        intro name
        simpa only [ordinary_names] using (rawNames name).trans (finalNames name).symm
      have lookups := compatible_lookup_all resultCompatible rawDomain
      have next : BindingAgreement
          (GeneralPremise.queryOutputNames arguments signature.modes ++ available).eraseDups final result :=
        bindingAgreement_of_lookups scopedUnique resultUnique rawNames
          (fun name => (ordinary_lookup final name).symm.trans (lookups name).symm)
      have tuple : row.values ∈ relEnv.tuples relation (arguments.map (applyBindings bindings)) := by
        rw [← signatureRelation]
        exact (reads signature signatureMember _ _).mpr ⟨row,List.mem_of_getElem? selected,rowTyped.1,rfl⟩
      exact ⟨result,
        RelationQueryAdmission.premiseStepWithEnv_relationQuery_of_env_tuple tuple matched merged,next⟩
  | dynamicRow registered _ _ _ _ _ _ _ =>
      rw [noDynamic] at registered
      cases registered

theorem query_toReference_bindings {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    {available : List String} {bindings : Bindings}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (noDynamic : environment.provider.dynamicRelations = [])
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (shapes : ∀ argument ∈ arguments,FirstOrder argument)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec available (.relationQuery relation arguments)).supported = true)
    (held : GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins) :
    ∃ result,result ∈ Engine.premiseStepWithEnv relEnv environment.language bindings
      (.relationQuery relation arguments) ∧ BindingAgreement
        (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
          available (.relationQuery relation arguments)).available final result := by
  exact query_toReference_bindings_recursive relEnv reads noDynamic (by rw [specification]; exact inferred_zero _)
    (binderFreeList_of_members (fun schema member => (shapes schema member).binderFree))
    agreement supported held


open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

/-- Completed bindings of recursive quantified validation retain exact
ordinary readback while the reference witnesses are constructed. -/
theorem validation_toReference_bindings {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (noDynamic : environment.provider.dynamicRelations = []) {premise : Premise}
    (shape : Validation premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial final : Assignment} {event : GeneralPremise.Event}
    {available : List String} {bindings : Bindings}
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      available premise).supported = true)
    (held : GeneralPremise.PremiseHolds environment context premise initial final event) :
    ∃ witness result,ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result := by
  induction shape generalizing context initial final available bindings event with
  | query _ shapes =>
      cases held with
      | query query =>
          obtain ⟨result,member,next⟩ :=
            query_toReference_bindings relEnv reads noDynamic specification shapes agreement supported query
          exact ⟨.base result,result,.base rfl member,next⟩
  | @freshness condition subjectShape =>
      cases held with
      | @freshness _ _ _ atom subject read fresh =>
          have roots := typed.rootValues (by rw [specification]; exact inferred_zero _)
          obtain ⟨named,subjectRead⟩ := freshness_readout specification subjectShape roots read
          have lookups : ∀ name,(ordinary initial).lookup name = bindings.lookup name :=
            fun name => (ordinary_lookup initial name).trans (agreement.lookups name)
          have rawNamed : resolveFreshVarName bindings condition.varName = some atom := by
            unfold resolveFreshVarName at named ⊢
            rw [← lookups]
            exact named
          have rawSubject : applyBindings bindings condition.term = subject :=
            (apply_eq_of_same_lookups subjectShape (fun name _ => (lookups name).symm)).trans subjectRead
          have member : bindings ∈ Engine.premiseStepWithEnv relEnv environment.language bindings
              (.freshness condition) := by
            simp only [Engine.premiseStepWithEnv,rawNamed,rawSubject]
            rw [if_pos (show Substitution.checkFreshness ⟨atom,subject⟩ = true from
              (GeneralPremise.syntactic_freshness_iff _ _).mpr fresh)]
            exact List.mem_singleton_self _
          exact ⟨.base bindings,bindings,.base rfl member,agreement⟩
  | @quantified collection parameter body bodyShape ih =>
      cases held with
      | @quantified _ _ _ _ _ _ kind elements _ read validated =>
          have finalEq := validated.final_eq_initial
          subst final
          have roots := typed.rootValues (by rw [specification]; exact inferred_zero _)
          have carrier : bindings.lookup collection = some (.collection kind elements none) :=
            ((ordinary_lookup initial collection).trans (agreement.lookups collection)).symm.trans
              (finiteCollection_lookup roots read)
          have localSupported : (GeneralPremise.premiseFlow environment.language environment.provider
              context.rule context.spec (parameter::available) body).supported = true := by
            have parts := supported
            simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at parts
            exact parts.2
          have bodies : ∀ (ordinal : Nat) {items : List Pattern}
              {events : List (Nat × Pattern × List GeneralPremise.Event)},
              GeneralPremise.QuantifiedElements environment context parameter body ordinal items
                initial initial events →
              ∃ witnesses,ReferenceStep.ForAllValid relEnv environment.language sites bindings
                parameter body items witnesses := by
            intro ordinal items
            induction items generalizing ordinal with
            | nil => intro events validated; exact ⟨[],.nil⟩
            | cons element elements tailIH =>
                intro events validated
                cases validated with
                | cons localTyped bodyHeld tail =>
                    obtain ⟨witness,result,bodyValid,_⟩ := ih (context := context.quantified)
                      specification localTyped
                      (bindingAgreement_bindParameter agreement parameter context.bound element)
                      localSupported bodyHeld
                    obtain ⟨witnesses,tailValid⟩ := tailIH _ tail
                    exact ⟨witness::witnesses,.cons bodyValid tailValid⟩
          obtain ⟨witnesses,bodiesValid⟩ := bodies 0 validated
          exact ⟨.forAll witnesses,bindings,.forAll carrier bodiesValid,agreement⟩

/-- Whole premise lists retain their actual completed assignment and exact
ordinary readback as reference witnesses are assembled left to right. -/
theorem premises_toReference_bindings {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (noDynamic : environment.provider.dynamicRelations = [])
    {context : GeneralPremise.Context} {premises : List Premise} {initial final : Assignment}
    {events : List GeneralPremise.Event} {available : List String} {bindings : Bindings}
    (sites : Pattern) (shapes : ∀ premise ∈ premises,Validation premise)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premisesFlow environment.language environment.provider context.rule context.spec
      available premises).supported = true)
    (held : GeneralPremise.PremisesHold environment context premises initial final events) :
    ∃ witnesses result,ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result := by
  induction premises generalizing context initial available bindings events with
  | nil =>
      cases held
      exact ⟨[],bindings,.nil bindings,agreement⟩
  | cons premise premises tailIH =>
      cases held with
      | cons head tail =>
          simp only [GeneralPremise.premisesFlow,Bool.and_eq_true] at supported ⊢
          obtain ⟨witness,middle,headValid,next⟩ := validation_toReference_bindings relEnv reads noDynamic
            (shapes premise (List.mem_cons_self ..)) sites specification typed agreement supported.1 head
          obtain ⟨witnesses,result,tailValid,completed⟩ := tailIH (context := context.next)
            (fun later member => shapes later (List.mem_cons_of_mem _ member)) specification
            (head.typed typed) next supported.2 tail
          exact ⟨witness::witnesses,result,.cons headValid tailValid,completed⟩

theorem firstOrder_notDeeper (sites : Pattern) {schema : Pattern} (shape : FirstOrder schema) :
    ReferenceStep.notDeeper sites 0 schema = true := by
  induction shape with
  | metavariable name =>
      simp only [ReferenceStep.notDeeper]
      split <;> simp
  | constructor label arguments children ih =>
      simp only [ReferenceStep.notDeeper]
      induction arguments with
      | nil => rfl
      | cons head tail tailIH =>
          simp only [ReferenceStep.notDeeperList,Bool.and_eq_true]
          exact ⟨ih head (List.mem_cons_self ..),tailIH
            (fun child member => children child (List.mem_cons_of_mem _ member))
            (fun child member => ih child (List.mem_cons_of_mem _ member))⟩

/-- Actual first-order root matching earns the ordinary matcher instance
and complete capture readback, despite different raw store order. -/
theorem matching_reference_bindings {rule : RewriteRule} {bound : List TypeExpr}
    {source : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (shape : FirstOrder rule.left)
    (matched : GeneralScopedMatchMachine.TracedMatches rule (GeneralRuleBindingInference.inferredSpec rule)
      bound.length .left [] 0 [] rule.left source trace captured)
    (roots : GeneralPremise.RootValues bound.length captured) :
    ∃ bindings,bindings ∈ matchPattern rule.left source ∧
      BindingAgreement rule.left.freeFvarNames captured bindings := by
  exact binderFree_matching_bindingAgreement shape.binderFree matched.matching roots

/-- Every actual typed scoped firing in the recursive validation domain
has an original reference rule witness with exactly its target and index. -/
theorem root_toReference {environment : GeneralPremise.Environment} {rule : RewriteRule}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (noDynamic : environment.provider.dynamicRelations = [])
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (left : FirstOrder rule.left) (right : FirstOrder rule.right)
    (shapes : ∀ premise ∈ rule.premises,Validation premise)
    (flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule
      (GeneralRuleBindingInference.inferredSpec rule) = true)
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index bindings witnesses) target := by
  cases fired with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ sourceTyped matched capturedTyped held reduct targetTyped =>
      have sameRule := Option.some.inj (actualDeclared.symm.trans declared)
      subst actualRule
      have sameSpec := Option.some.inj (actualSpecified.symm.trans specified)
      subst actualSpec
      have roots := capturedTyped.rootValues (inferred_zero _)
      obtain ⟨bindings,rawMatched,captures⟩ := matching_reference_bindings left matched roots
      simp only [GeneralPremise.rulePremisesAdmitted,Bool.and_eq_true] at flow
      obtain ⟨witnesses,result,premisesValid,completedReadback⟩ := premises_toReference_bindings relEnv reads
        noDynamic (ReferenceStep.captureSites rule) shapes rfl capturedTyped captures flow.1 held
      have completedRoots := (held.typed capturedTyped).rootValues (inferred_zero _)
      have rhs : applyBindings (ordinary completed) rule.right = target :=
        instantiation_readout right completedRoots reduct
      have ordinaryRhs : applyBindings result rule.right = target :=
        (apply_eq_of_same_lookups right (fun name _ =>
          (completedReadback.lookups name).symm.trans (ordinary_lookup completed name).symm)).trans rhs
      have scopedRhs : Match.applyBindingsScoped (ReferenceStep.captureSites rule) result 0 rule.right =
          target :=
        (ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _
          (firstOrder_notDeeper _ right)).trans ordinaryRhs
      rw [← scopedRhs]
      exact ⟨bindings,witnesses,.rule declared (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic]
        using rawMatched) premisesValid⟩

#print axioms validation_toReference_bindings
#print axioms premises_toReference_bindings
#print axioms firstOrder_notDeeper
#print axioms matching_reference_bindings
#print axioms root_toReference


theorem bindingAgreement_scopedCompatible {ambient : Nat} {names : List String}
    {assignment : Assignment} {bindings : Bindings}
    (agreement : BindingAgreement names assignment bindings)
    (roots : GeneralPremise.RootValues ambient assignment) :
    ScopedCompatible ambient bindings assignment := by
  rintro ⟨key,value⟩ member
  have found := ordinary_lookup_member agreement.scopedUnique member
  obtain ⟨dependencies,caller,_⟩ := roots key value found
  have read := agreement.lookups key
  rw [found,Option.map_some] at read
  exact ⟨dependencies,caller,read.symm⟩

/-- Exact raw/scoped readback transports the actual captured typing,
object representation and canonical metadata to every raw binding value. -/
theorem bindingAgreement_capturesTyped {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {names : List String} {assignment : Assignment} {bindings : Bindings}
    (typed : GeneralPremise.TypedAssignment environment context assignment)
    (canonical : GeneralPremise.CanonicalValues assignment)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (agreement : BindingAgreement names assignment bindings) :
    CapturesTyped environment.language environment.free context.bound context.rule.typeContext bindings := by
  intro entry member
  have rawFound := bindings_lookup_of_mem agreement.ordinaryUnique member
  obtain ⟨value,found,body⟩ := Option.map_eq_some_iff.mp ((agreement.lookups entry.1).trans rawFound)
  have sourceMember := ConditionalEquationExecution.lookup_assignment_member assignment entry.1 value found
  obtain ⟨dependencies,expected,declared,sorted,_,_,bodyTyped⟩ := typed.1 entry.1 value sourceMember
  have empty := GeneralPremise.checkZeroDependencies_sound context.spec zero entry.1 dependencies declared
  rw [empty,List.nil_append] at bodyTyped
  exact ⟨expected,sorted,body ▸ bodyTyped,body ▸ canonical _ _ found,
    body ▸ typed.2 _ _ sourceMember,body ▸ bodyTyped.isWellScopedAt⟩

/-- Literal reference queries recover the actual typed scoped query and
all completed bindings. The source and raw stores retain different orders. -/
theorem query_fromReference_bindings {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {relation : String} {arguments : List Pattern}
    {initial : Assignment} {bindings result : Bindings} {available : List String}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (distinct : relation ≠ "eq")
    (locations : ∀ position schema,arguments[position]? = some schema →
      sitePattern? context.rule (context.site position) = some schema)
    (shapes : ∀ argument ∈ arguments,FirstOrder argument)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (canonical : GeneralPremise.CanonicalValues initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      available (.relationQuery relation arguments)).supported = true)
    (member : result ∈ Engine.premiseStepWithEnv relEnv environment.language bindings
      (.relationQuery relation arguments)) :
    ∃ final rowIndex origins,GeneralPremise.TracedQuery environment context relation arguments initial rowIndex
      final origins ∧ BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available (.relationQuery relation arguments)).available final result := by
  cases declared : GeneralPremise.signature? environment.provider relation arguments.length with
  | none => simp [GeneralPremise.premiseFlow,declared] at supported
  | some signature =>
      have checked := supported
      simp only [GeneralPremise.premiseFlow,declared,Bool.and_eq_true] at checked
      have schemasTyped := GeneralPremise.schemaValuesChecked_sound checked.2
      rw [lookupRuleType_eq] at schemasTyped
      have availableBound := bindingAgreement_available agreement
      have inputs : GeneralPremise.BoundNames initial
          (GeneralPremise.queryInputNames arguments signature.modes) :=
        fun name member => availableBound name (GeneralPremise.namesAvailable_sound _ _ checked.1 name member)
      have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
        rw [specification]
        exact inferred_zero _
      obtain ⟨final,rowIndex,origins,traced,compatible,_⟩ := query_fromReference relEnv reads valid providerClosed
        specification contextUnique distinct declared locations shapes schemasTyped inputs
        (bindingAgreement_capturesTyped typed canonical zero agreement)
        (bindingAgreement_scopedCompatible agreement (typed.rootValues zero)) member
      have sourceEvent : GeneralPremise.PremiseHolds environment context (.relationQuery relation arguments)
          initial final (.query context.premiseIndex context.quantifierDepth rowIndex origins) := .query traced
      have finalBound := sourceEvent.bindingFlow available availableBound
      have finalUnique : (final.map Prod.fst).Nodup := by
        cases traced with
        | row _ _ _ arguments _ => exact query_arguments_unique shapes arguments.readout agreement.scopedUnique
        | dynamicRow _ _ _ _ _ _ arguments _ =>
            exact query_arguments_unique shapes arguments.readout agreement.scopedUnique
      obtain ⟨tuple,extension,_,matched,merged⟩ :=
        ConditionalEquationExecution.relationQueryStep_readout relEnv environment.language bindings result
          relation arguments member
      have rawUnique := mergeBindings_nodup merged agreement.ordinaryUnique
      have lengths : arguments.length = signature.modes.length :=
        (GeneralPremise.signature?_readout _ _ _ _ declared).2.2.2.symm
      have rawNames : ∀ name ∈ result.map Prod.fst,name ∈
          (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
            available (.relationQuery relation arguments)).available := by
        intro name present
        obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp present
        simp only [GeneralPremise.premiseFlow,declared,List.mem_eraseDups,List.mem_append]
        rcases List.mem_append.mp (merge_members merged stored) with earlier | produced
        · exact Or.inr ((agreement.ordinaryNames entry.1).mp (List.mem_map_of_mem earlier))
        · rcases query_names_cover lengths _ (relationArgs_names shapes matched entry produced) with input | output
          · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ checked.1 _ input)
          · exact Or.inl output
      exact ⟨final,rowIndex,origins,traced,
        bindingAgreement_of_scopedCompatible compatible finalUnique rawUnique finalBound rawNames⟩

private theorem valuesTyped_object_scope {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {values : List Pattern} {types : List TypeExpr}
    (typed : GeneralPremise.ValuesTyped language free bound values types) :
    ∀ value ∈ values,isObjectPattern value = true ∧ value.isWellScopedAt bound.length = true := by
  induction typed with
  | nil => intro _ member; cases member
  | cons first rest ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨first.2.2.1,first.2.2.2⟩
    · exact ih value later

/-- Original provider evidence reconstructs the actual recursive output
continuation. The chosen raw store's typing is derived from the current store,
the original tuple match and the checked provider row. Literal input eligibility
is explicit; no completed-outcome or whole-query agreement is assumed. -/
theorem query_fromReference_recursive {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {relation : String} {arguments : List Pattern} {initial : Assignment}
    {current result : Bindings} {signature : GeneralPremise.Signature}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free environment.provider = true)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (distinct : relation ≠ "eq")
    (signatureFound : GeneralPremise.signature? environment.provider relation arguments.length = some signature)
    (locations : ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
      sitePattern? context.rule (context.site position) = some schema)
    (shapes : binderFreeList arguments = true)
    (inputShapes : ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
      signature.modes[position]? = some RelationArgMode.input → FirstOrder schema)
    (inputReady : ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
      signature.modes[position]? = some RelationArgMode.input →
      GeneralPremise.checkRootProjectionSchema context.rule context.spec (context.site position) [] schema = true)
    (schemasTyped : List.Forall₂ (Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList context.rule.typeContext) []) arguments signature.argumentTypes)
    (inputs : GeneralPremise.BoundNames initial (GeneralPremise.queryInputNames arguments signature.modes))
    (currentTyped : CapturesTyped environment.language environment.free context.bound context.rule.typeContext current)
    (before : ScopedCompatible context.bound.length current initial)
    (member : result ∈ Engine.premiseStepWithEnv relEnv environment.language current (.relationQuery relation arguments)) :
    ∃ final rowIndex origins,GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins ∧
      ScopedCompatible context.bound.length result final ∧
      CapturesTyped environment.language environment.free context.bound context.rule.typeContext result := by
  obtain ⟨tuple,extension,provided,matched,merged⟩ :=
    ConditionalEquationExecution.relationQueryStep_readout relEnv environment.language current result relation arguments member
  rw [builtinRelationTuples_eq_nil distinct,List.nil_append] at provided
  obtain ⟨signatureMember,signatureRelation,_,modesLength⟩ :=
    GeneralPremise.signature?_readout _ _ _ _ signatureFound
  rw [← signatureRelation] at provided
  obtain ⟨row,rowMember,rowRelation,rowValues⟩ := (reads signature signatureMember _ _).mp provided
  subst rowValues
  have tupleLength := matchRelationArgs_lengths matched
  obtain ⟨closedSignature,closedFound,closedTyped⟩ :=
    GeneralPremise.checkProviderClosed_row _ _ _ providerClosed row rowMember
  have sameSignature : closedSignature = signature := by
    rw [rowRelation,signatureRelation,← tupleLength,signatureFound] at closedFound
    exact (Option.some.inj closedFound).symm
  subst closedSignature
  have rowTyped := GeneralPremise.closed_row_in_bound closedTyped context.bound
  have extensionTyped := relationArgs_typed_recursive valid choices shapes matched schemasTyped rowTyped.2
  have resultTyped := capturesTyped_merge currentTyped extensionTyped merged
  have lifted : ScopedCompatible context.bound.length result initial :=
    compatible_lift before (fun _ _ found => merge_lookup_left merged found)
  obtain ⟨final,origins,traced,compatible,_,_⟩ := tracedArguments_construct_recursive context admitted zero resultTyped
    arguments signature.modes 0 shapes modesLength.symm (by simpa only [Nat.zero_add] using locations)
    inputShapes (by simpa only [Nat.zero_add] using inputReady) (valuesTyped_object_scope rowTyped.2)
    matched (fun _ _ found => mergeBindings_subsumed_left merged found)
    (fun _ _ found => mergeBindings_subsumed_right merged found) inputs lifted
  obtain ⟨rowIndex,selected⟩ := List.mem_iff_getElem?.mp rowMember
  have finalTyped : GeneralPremise.TypedAssignment environment context final :=
    compatible.typed_admitted resultTyped admitted zero
  exact ⟨final,rowIndex,origins,.row selected signatureFound rowTyped traced finalTyped,compatible,resultTyped⟩


/-- Preserve every rest role checked by the actual ordered schema gate. -/
theorem schemaValuesChecked_restAware {language : LanguageDef} {rule : RewriteRule}
    {bound : List TypeExpr} {patterns : List Pattern} {types : List TypeExpr}
    (shapes : binderFreeList patterns = true)
    (checked : GeneralPremise.schemaValuesChecked language rule bound patterns types = true) :
    List.Forall₂ (Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language
      (FreeTypeContext.ofList rule.typeContext) bound) patterns types := by
  induction patterns generalizing types with
  | nil => cases types with
    | nil => exact .nil
    | cons type types => simp [GeneralPremise.schemaValuesChecked] at checked
  | cons pattern patterns ih =>
    cases types with
    | nil => simp [GeneralPremise.schemaValuesChecked] at checked
    | cons type types =>
      obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
      simp only [GeneralPremise.schemaValuesChecked,Bool.and_eq_true] at checked
      have head := binderFree_schema_restAware headShape checked.1
      rw [lookupRuleType_eq] at head
      exact .cons head (ih tailShapes checked.2)

/-- The existing static input checker supplies the exact actual projection
site for any selected input; output positions require no input read. -/
theorem queryInputs_projection_at {rule : RewriteRule} {spec : RuleBindingSpec}
    {premiseIndex quantifierDepth : Nat} {available : List String}
    {schemas : List Pattern} {modes : List RelationArgMode} {index position : Nat} {schema : Pattern}
    (checked : GeneralPremise.Static.checkQueryInputs rule spec premiseIndex quantifierDepth available index schemas modes = true)
    (selected : schemas[position]? = some schema) (input : modes[position]? = some RelationArgMode.input) :
    GeneralPremise.checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth (index+position)) [] schema = true := by
  induction position generalizing schemas modes index with
  | zero =>
    cases schemas with
    | nil => cases selected
    | cons first rest =>
      cases modes with
      | nil => cases input
      | cons mode modes =>
        cases Option.some.inj selected
        have same := Option.some.inj input
        subst mode
        simp only [GeneralPremise.Static.checkQueryInputs,Bool.and_eq_true] at checked
        simpa only [Nat.add_zero] using checked.1.1
  | succ position ih =>
    cases schemas with
    | nil => simp at selected
    | cons first rest =>
      cases modes with
      | nil => simp at input
      | cons mode modes =>
        have tail : GeneralPremise.Static.checkQueryInputs rule spec premiseIndex quantifierDepth available
            (index+1) rest modes = true := by
          cases mode <;> simp only [GeneralPremise.Static.checkQueryInputs,Bool.and_eq_true,Bool.true_and] at checked
          · exact checked.2
          · exact checked
        have later := ih tail (by simpa using selected) (by simpa using input)
        simpa only [Nat.add_assoc,Nat.add_comm 1 position,Nat.succ_eq_add_one] using later

private theorem query_arguments_unique_recursive {context : GeneralPremise.Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins)
    (unique : (initial.map Prod.fst).Nodup) : (final.map Prod.fst).Nodup := by
  induction held with
  | nil => exact unique
  | input _ _ ih => exact ih unique
  | output matched _ ih => exact ih (matching_unique_names_recursive matched.matching unique).1

/-- Reverse source query coverage for recursive outputs with explicitly
eligible literal inputs. Actual ordered admission supplies schema rest roles
and projection sites; the tuple and provider earn the complete final store. -/
theorem query_fromReference_bindings_recursive {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {relation : String} {arguments : List Pattern}
    {initial : Assignment} {bindings result : Bindings} {available : List String}
    {refinement : GeneralPremise.Static.Refinement}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free environment.provider = true)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (distinct : relation ≠ "eq")
    (locations : ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
      sitePattern? context.rule (context.site position) = some schema)
    (shapes : binderFreeList arguments = true)
    (inputShapes : ∀ signature,GeneralPremise.signature? environment.provider relation arguments.length = some signature →
      ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
        signature.modes[position]? = some RelationArgMode.input → FirstOrder schema)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (canonical : GeneralPremise.CanonicalValues initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      available (.relationQuery relation arguments)).supported = true)
    (staticSupported : (GeneralPremise.Static.premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement (.relationQuery relation arguments)).supported = true)
    (member : result ∈ Engine.premiseStepWithEnv relEnv environment.language bindings (.relationQuery relation arguments)) :
    ∃ final rowIndex origins,GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
        available (.relationQuery relation arguments)).available final result := by
  cases declared : GeneralPremise.signature? environment.provider relation arguments.length with
  | none => simp [GeneralPremise.premiseFlow,declared] at supported
  | some signature =>
    have checked := supported
    simp only [GeneralPremise.premiseFlow,declared,Bool.and_eq_true] at checked
    have schemasTyped := schemaValuesChecked_restAware shapes checked.2
    have availableBound := bindingAgreement_available agreement
    have inputs : GeneralPremise.BoundNames initial (GeneralPremise.queryInputNames arguments signature.modes) :=
      fun name present => availableBound name (GeneralPremise.namesAvailable_sound _ _ checked.1 name present)
    have inputChecks : GeneralPremise.Static.checkQueryInputs context.rule context.spec context.premiseIndex
        context.quantifierDepth refinement.available 0 arguments signature.modes = true := by
      simpa only [GeneralPremise.Static.premiseFlow,declared] using staticSupported
    have projections : ∀ (position : Nat) (schema : Pattern),arguments[position]? = some schema →
        signature.modes[position]? = some RelationArgMode.input →
        GeneralPremise.checkRootProjectionSchema context.rule context.spec (context.site position) [] schema = true := by
      intro position schema selected input
      simpa only [GeneralPremise.Context.site,Nat.zero_add] using queryInputs_projection_at inputChecks selected input
    obtain ⟨final,rowIndex,origins,traced,compatible,_⟩ := query_fromReference_recursive relEnv reads valid choices
      providerClosed admitted zero distinct declared locations shapes (inputShapes signature declared) projections schemasTyped inputs
      (bindingAgreement_capturesTyped typed canonical zero agreement)
      (bindingAgreement_scopedCompatible agreement (typed.rootValues zero)) member
    have sourceEvent : GeneralPremise.PremiseHolds environment context (.relationQuery relation arguments)
        initial final (.query context.premiseIndex context.quantifierDepth rowIndex origins) := .query traced
    have finalBound := sourceEvent.bindingFlow available availableBound
    have finalUnique : (final.map Prod.fst).Nodup := by
      cases traced with
      | row _ _ _ arguments _ => exact query_arguments_unique_recursive arguments agreement.scopedUnique
      | dynamicRow _ _ _ _ _ _ arguments _ => exact query_arguments_unique_recursive arguments agreement.scopedUnique
    obtain ⟨tuple,extension,_,matched,merged⟩ :=
      ConditionalEquationExecution.relationQueryStep_readout relEnv environment.language bindings result relation arguments member
    have rawUnique := mergeBindings_nodup merged agreement.ordinaryUnique
    have lengths : arguments.length = signature.modes.length :=
      (GeneralPremise.signature?_readout _ _ _ _ declared).2.2.2.symm
    have rawNames : ∀ name ∈ result.map Prod.fst,name ∈
        (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
          available (.relationQuery relation arguments)).available := by
      intro name present
      obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp present
      simp only [GeneralPremise.premiseFlow,declared,List.mem_eraseDups,List.mem_append]
      rcases List.mem_append.mp (merge_members merged stored) with earlier | produced
      · exact Or.inr ((agreement.ordinaryNames entry.1).mp (List.mem_map_of_mem earlier))
      · rcases query_names_cover lengths _ (relationArgs_names_recursive matched entry produced) with input | output
        · exact Or.inr (GeneralPremise.namesAvailable_sound _ _ checked.1 _ input)
        · exact Or.inl output
    exact ⟨final,rowIndex,origins,traced,
      bindingAgreement_of_scopedCompatible compatible finalUnique rawUnique finalBound rawNames⟩

#print axioms schemaValuesChecked_restAware
#print axioms queryInputs_projection_at
#print axioms query_arguments_unique_recursive
#print axioms query_fromReference_bindings_recursive

#print axioms query_fromReference_recursive

#print axioms bindingAgreement_scopedCompatible
#print axioms bindingAgreement_capturesTyped
#print axioms query_fromReference_bindings


/-- Original literal validation reconstructs real retained continuations for
recursive schemas. Actual provider modes delimit the conservative input
domain; original occurrence tables and local quantified histories remain. -/
theorem validation_fromReference_bindings_recursive {Schema : Pattern → Prop}
    (schemaBinderFree : ∀ schema,Schema schema → binderFree schema = true)
    {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    {premise : Premise} (shape : ValidationWith Schema premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings} {witness : ReferenceStep.Witness}
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (inputShapes : FirstOrderQueryInputs environment.provider premise)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (located : Located context premise)
    (ordinarySupported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec available premise).supported = true)
    (staticSupported : (GeneralPremise.Static.premiseFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported = true)
    (held : ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result) :
    ∃ final event,GeneralPremise.PremiseHolds environment context premise initial final event ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result := by
  induction shape generalizing context initial available refinement bindings result witness with
  | query distinct shapes =>
      cases held with
      | base _ member =>
          obtain ⟨final,rowIndex,origins,traced,completed⟩ := query_fromReference_bindings_recursive relEnv reads valid
            choices providerClosed admitted zero distinct (fun _ _ selected => located.query selected)
            (binderFreeList_of_members (fun schema member => schemaBinderFree schema (shapes schema member)))
            inputShapes facts.typed facts.canonical agreement ordinarySupported staticSupported member
          exact ⟨final,_,.query traced,completed⟩
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | @freshness condition subjectShape =>
      cases held with
      | base _ member =>
          have sameResult := Engine.premiseStepWithEnv_freshness_mem member
          subst result
          obtain ⟨atom,subject,read⟩ := GeneralPremise.Static.freshness_total
            facts.typed zero facts.represented staticSupported
          obtain ⟨named,subjectRead⟩ := freshness_readout_recursive (schemaBinderFree _ subjectShape)
            (facts.typed.rootValues zero) read
          have lookups : ∀ name,(ordinary initial).lookup name = bindings.lookup name :=
            fun name => (ordinary_lookup initial name).trans (agreement.lookups name)
          have rawNamed : resolveFreshVarName bindings condition.varName = some atom := by
            unfold resolveFreshVarName at named ⊢
            rw [← lookups]
            exact named
          have rawSubject : applyBindings bindings condition.term = subject :=
            (applyBindings_eq_of_lookup_agreement _ (fun name _ => (lookups name).symm)).trans subjectRead
          obtain ⟨actualAtom,actualNamed,fresh⟩ := Engine.premiseStepWithEnv_freshness_check member
          change resolveFreshVarName bindings condition.varName = some actualAtom at actualNamed
          have atomSame := Option.some.inj (actualNamed.symm.trans rawNamed)
          subst actualAtom
          rw [rawSubject] at fresh
          exact ⟨initial,_,.freshness read ((GeneralPremise.syntactic_freshness_iff _ _).mp fresh),agreement⟩
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | @quantified collection parameter body bodyShape ih =>
      cases held with
      | base shape _ => simp [ReferenceStep.isBase] at shape
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
      | @forAll _ _ _ _ _ kind elements witnesses selected bodies =>
          have read : GeneralPremise.finiteCollection? context.bound.length initial collection =
              some (kind,elements) := by
            rw [finiteCollection_readout (facts.typed.rootValues zero),ordinary_lookup,agreement.lookups,selected]
            rfl
          simp only [GeneralPremise.Static.premiseFlow,Bool.and_eq_true] at staticSupported
          split at staticSupported <;> try simp at staticSupported
          rename_i declaredKind elementType parameterType collectionDeclared parameterDeclared
          have typeSame := staticSupported.1.2.1
          subst parameterType
          have parameterDependencies := staticSupported.1.2.2
          have localStatic := staticSupported.2
          have localOrdinary : (GeneralPremise.premiseFlow environment.language environment.provider
              context.rule context.spec (parameter::available) body).supported = true := by
            have parts := ordinarySupported
            simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at parts
            exact parts.2
          obtain ⟨elementsTyped,objects⟩ := GeneralPremise.finiteCollection_elements_typed
            facts.typed zero collectionDeclared read
          have canonical := GeneralPremise.finiteCollection?_canonical facts.canonical read
          have sourceElements : ∀ (ordinal : Nat) {items : List Pattern} {proofs : List ReferenceStep.Witness},
              ReferenceStep.ForAllValid relEnv environment.language sites bindings parameter body items proofs →
              ElementsHaveType environment.language environment.free context.bound items elementType →
              isObjectPatternList items = true → Pattern.hasCanonicalBinderMetadataList items = true →
              ∃ events,GeneralPremise.QuantifiedElements environment context parameter body ordinal items
                initial initial events := by
            intro ordinal items
            induction items generalizing ordinal with
            | nil => intro _ _ _ _ _; exact ⟨[],.nil⟩
            | cons element elements tailIH =>
                intro proofs validated typedElements elementObjects elementCanonical
                cases validated with
                | cons bodyValid tail =>
                    cases typedElements with
                    | cons elementTyped tailTyped =>
                        simp only [isObjectPatternList,Bool.and_eq_true] at elementObjects
                        simp only [Pattern.hasCanonicalBinderMetadataList,Bool.and_eq_true] at elementCanonical
                        have localTyped := facts.typed.bindParameter parameterDeclared parameterDependencies
                          elementTyped elementObjects.1
                        have localFacts : GeneralPremise.Static.InputFacts environment context.quantified
                            (GeneralPremise.Static.localRefinement refinement parameter)
                            (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element)
                              initial) :=
                          ⟨localTyped,facts.canonical.bindParameter parameter elementCanonical.1,
                            facts.represented.bindParameter parameter _⟩
                        obtain ⟨localFinal,event,sourceBody,_⟩ := ih (context := context.quantified)
                          admitted zero inputShapes contextUnique localFacts
                          (bindingAgreement_bindParameter agreement parameter context.bound element)
                          located.quantified localOrdinary localStatic bodyValid
                        obtain ⟨events,sourceTail⟩ := tailIH (ordinal + 1) tail tailTyped elementObjects.2
                          elementCanonical.2
                        exact ⟨(ordinal,element,[event])::events,.cons localTyped sourceBody sourceTail⟩
          obtain ⟨events,sourceElements⟩ := sourceElements 0 bodies elementsTyped objects canonical
          exact ⟨initial,_,.quantified read sourceElements,agreement⟩


#print axioms validation_fromReference_bindings_recursive

/-- Original reference validation reconstructs the ordinary typed scoped
derivation and preserves all completed binding lookups and domains. -/
theorem validation_fromReference_bindings {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    {premise : Premise} (shape : Validation premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings} {witness : ReferenceStep.Witness}
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (located : Located context premise)
    (ordinarySupported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec available premise).supported = true)
    (staticSupported : (GeneralPremise.Static.premiseFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported = true)
    (held : ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result) :
    ∃ final event,GeneralPremise.PremiseHolds environment context premise initial final event ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result := by
  induction shape generalizing context initial available refinement bindings result witness with
  | query distinct shapes =>
      cases held with
      | base _ member =>
          obtain ⟨final,rowIndex,origins,traced,completed⟩ := query_fromReference_bindings relEnv reads valid
            providerClosed specification contextUnique distinct (fun _ _ selected => located.query selected)
            shapes facts.typed facts.canonical agreement ordinarySupported member
          exact ⟨final,_,.query traced,completed⟩
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | @freshness condition subjectShape =>
      cases held with
      | base _ member =>
          have sameResult := Engine.premiseStepWithEnv_freshness_mem member
          subst result
          have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
            rw [specification]
            exact inferred_zero _
          obtain ⟨atom,subject,read⟩ := GeneralPremise.Static.freshness_total
            facts.typed zero facts.represented staticSupported
          obtain ⟨named,subjectRead⟩ := freshness_readout specification subjectShape
            (facts.typed.rootValues zero) read
          have lookups : ∀ name,(ordinary initial).lookup name = bindings.lookup name :=
            fun name => (ordinary_lookup initial name).trans (agreement.lookups name)
          have rawNamed : resolveFreshVarName bindings condition.varName = some atom := by
            unfold resolveFreshVarName at named ⊢
            rw [← lookups]
            exact named
          have rawSubject : applyBindings bindings condition.term = subject :=
            (apply_eq_of_same_lookups subjectShape (fun name _ => (lookups name).symm)).trans subjectRead
          obtain ⟨actualAtom,actualNamed,fresh⟩ := Engine.premiseStepWithEnv_freshness_check member
          change resolveFreshVarName bindings condition.varName = some actualAtom at actualNamed
          have atomSame := Option.some.inj (actualNamed.symm.trans rawNamed)
          subst actualAtom
          rw [rawSubject] at fresh
          exact ⟨initial,_,.freshness read ((GeneralPremise.syntactic_freshness_iff _ _).mp fresh),agreement⟩
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | @quantified collection parameter body bodyShape ih =>
      cases held with
      | base shape _ => simp [ReferenceStep.isBase] at shape
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
      | @forAll _ _ _ _ _ kind elements witnesses selected bodies =>
          have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
            rw [specification]
            exact inferred_zero _
          have read : GeneralPremise.finiteCollection? context.bound.length initial collection =
              some (kind,elements) := by
            rw [finiteCollection_readout (facts.typed.rootValues zero),ordinary_lookup,agreement.lookups,selected]
            rfl
          simp only [GeneralPremise.Static.premiseFlow,Bool.and_eq_true] at staticSupported
          split at staticSupported <;> try simp at staticSupported
          rename_i declaredKind elementType parameterType collectionDeclared parameterDeclared
          have typeSame := staticSupported.1.2.1
          subst parameterType
          have parameterDependencies := staticSupported.1.2.2
          have localStatic := staticSupported.2
          have localOrdinary : (GeneralPremise.premiseFlow environment.language environment.provider
              context.rule context.spec (parameter::available) body).supported = true := by
            have parts := ordinarySupported
            simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at parts
            exact parts.2
          obtain ⟨elementsTyped,objects⟩ := GeneralPremise.finiteCollection_elements_typed
            facts.typed zero collectionDeclared read
          have canonical := GeneralPremise.finiteCollection?_canonical facts.canonical read
          have sourceElements : ∀ (ordinal : Nat) {items : List Pattern} {proofs : List ReferenceStep.Witness},
              ReferenceStep.ForAllValid relEnv environment.language sites bindings parameter body items proofs →
              ElementsHaveType environment.language environment.free context.bound items elementType →
              isObjectPatternList items = true → Pattern.hasCanonicalBinderMetadataList items = true →
              ∃ events,GeneralPremise.QuantifiedElements environment context parameter body ordinal items
                initial initial events := by
            intro ordinal items
            induction items generalizing ordinal with
            | nil => intro _ _ _ _ _; exact ⟨[],.nil⟩
            | cons element elements tailIH =>
                intro proofs validated typedElements elementObjects elementCanonical
                cases validated with
                | cons bodyValid tail =>
                    cases typedElements with
                    | cons elementTyped tailTyped =>
                        simp only [isObjectPatternList,Bool.and_eq_true] at elementObjects
                        simp only [Pattern.hasCanonicalBinderMetadataList,Bool.and_eq_true] at elementCanonical
                        have localTyped := facts.typed.bindParameter parameterDeclared parameterDependencies
                          elementTyped elementObjects.1
                        have localFacts : GeneralPremise.Static.InputFacts environment context.quantified
                            (GeneralPremise.Static.localRefinement refinement parameter)
                            (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound element)
                              initial) :=
                          ⟨localTyped,facts.canonical.bindParameter parameter elementCanonical.1,
                            facts.represented.bindParameter parameter _⟩
                        obtain ⟨localFinal,event,sourceBody,_⟩ := ih (context := context.quantified)
                          specification contextUnique localFacts
                          (bindingAgreement_bindParameter agreement parameter context.bound element)
                          located.quantified localOrdinary localStatic bodyValid
                        obtain ⟨events,sourceTail⟩ := tailIH (ordinal + 1) tail tailTyped elementObjects.2
                          elementCanonical.2
                        exact ⟨(ordinal,element,[event])::events,.cons localTyped sourceBody sourceTail⟩
          obtain ⟨events,sourceElements⟩ := sourceElements 0 bodies elementsTyped objects canonical
          exact ⟨initial,_,.quantified read sourceElements,agreement⟩

/-- Reference premise lists reconstruct actual ordered scoped histories and
completed binding readback under the original occurrence metadata. -/
theorem premises_fromReference_bindings_recursive {Schema : Pattern → Prop}
    (schemaBinderFree : ∀ schema,Schema schema → binderFree schema = true)
    {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    {context : GeneralPremise.Context} {premises : List Premise} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings}
    {witnesses : List ReferenceStep.Witness} (sites : Pattern)
    (shapes : ∀ premise ∈ premises,ValidationWith Schema premise)
    (locations : ∀ offset premise,premises[offset]? = some premise →
      context.rule.premises[context.premiseIndex + offset]? = some premise)
    (depthZero : context.quantifierDepth = 0)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (inputShapes : ∀ premise ∈ premises,FirstOrderQueryInputs environment.provider premise)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (ordinarySupported : (GeneralPremise.premisesFlow environment.language environment.provider
      context.rule context.spec available premises).supported = true)
    (staticSupported : (GeneralPremise.Static.premisesFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex refinement premises).supported = true)
    (held : ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result) :
    ∃ final history,GeneralPremise.PremisesHold environment context premises initial final history ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result := by
  induction premises generalizing context initial available refinement bindings witnesses with
  | nil =>
      cases held
      exact ⟨initial,[],.nil,agreement⟩
  | cons premise premises tailIH =>
      cases held with
      | cons head tail =>
          simp only [GeneralPremise.premisesFlow,Bool.and_eq_true] at ordinarySupported
          simp only [GeneralPremise.Static.premisesFlow,Bool.and_eq_true] at staticSupported
          have here : context.rule.premises[context.premiseIndex]? = some premise := by
            simpa only [Nat.add_zero] using locations 0 premise rfl
          have located : Located context premise := by
            simp only [Located,here,depthZero,Option.bind_some,quantifiedBody?]
          have headStatic : (GeneralPremise.Static.premiseFlow environment.language environment.provider
              context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported =
                true := by simpa only [depthZero] using staticSupported.1
          obtain ⟨middle,event,sourceHead,next⟩ := validation_fromReference_bindings_recursive schemaBinderFree
            relEnv reads valid choices providerClosed (shapes premise (List.mem_cons_self ..)) sites
            admitted zero (inputShapes premise (List.mem_cons_self ..)) contextUnique facts agreement located
            ordinarySupported.1 headStatic head
          have tailLocations : ∀ offset later,premises[offset]? = some later →
              context.next.rule.premises[context.next.premiseIndex + offset]? = some later := by
            intro offset later selected
            simpa only [GeneralPremise.Context.next,Nat.add_assoc,Nat.add_comm 1 offset]
              using locations (offset + 1) later selected
          have after := facts.afterPremise sourceHead
          have nextFacts : GeneralPremise.Static.InputFacts environment context.next
              (GeneralPremise.Static.premiseFlow environment.language environment.provider context.rule context.spec
                context.premiseIndex 0 refinement premise).refinement middle :=
            ⟨after.typed,after.canonical,by simpa only [depthZero] using after.represented⟩
          obtain ⟨final,history,sourceTail,completed⟩ := tailIH (context := context.next)
            (fun later member => shapes later (List.mem_cons_of_mem _ member)) tailLocations rfl admitted zero
            (fun later member => inputShapes later (List.mem_cons_of_mem _ member))
            contextUnique nextFacts next ordinarySupported.2 staticSupported.2 tail
          exact ⟨final,event::history,.cons sourceHead sourceTail,completed⟩


#print axioms premises_fromReference_bindings_recursive

/-- Reference premise lists reconstruct actual ordered scoped histories and
completed binding readback under the original occurrence metadata. -/
theorem premises_fromReference_bindings {environment : GeneralPremise.Environment}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    {context : GeneralPremise.Context} {premises : List Premise} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings}
    {witnesses : List ReferenceStep.Witness} (sites : Pattern)
    (shapes : ∀ premise ∈ premises,Validation premise)
    (locations : ∀ offset premise,premises[offset]? = some premise →
      context.rule.premises[context.premiseIndex + offset]? = some premise)
    (depthZero : context.quantifierDepth = 0)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (ordinarySupported : (GeneralPremise.premisesFlow environment.language environment.provider
      context.rule context.spec available premises).supported = true)
    (staticSupported : (GeneralPremise.Static.premisesFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex refinement premises).supported = true)
    (held : ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result) :
    ∃ final history,GeneralPremise.PremisesHold environment context premises initial final history ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result := by
  induction premises generalizing context initial available refinement bindings witnesses with
  | nil =>
      cases held
      exact ⟨initial,[],.nil,agreement⟩
  | cons premise premises tailIH =>
      cases held with
      | cons head tail =>
          simp only [GeneralPremise.premisesFlow,Bool.and_eq_true] at ordinarySupported
          simp only [GeneralPremise.Static.premisesFlow,Bool.and_eq_true] at staticSupported
          have here : context.rule.premises[context.premiseIndex]? = some premise := by
            simpa only [Nat.add_zero] using locations 0 premise rfl
          have located : Located context premise := by
            simp only [Located,here,depthZero,Option.bind_some,quantifiedBody?]
          have headStatic : (GeneralPremise.Static.premiseFlow environment.language environment.provider
              context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported =
                true := by simpa only [depthZero] using staticSupported.1
          obtain ⟨middle,event,sourceHead,next⟩ := validation_fromReference_bindings relEnv reads valid providerClosed
            (shapes premise (List.mem_cons_self ..)) sites specification contextUnique facts agreement located
            ordinarySupported.1 headStatic head
          have tailLocations : ∀ offset later,premises[offset]? = some later →
              context.next.rule.premises[context.next.premiseIndex + offset]? = some later := by
            intro offset later selected
            simpa only [GeneralPremise.Context.next,Nat.add_assoc,Nat.add_comm 1 offset]
              using locations (offset + 1) later selected
          have after := facts.afterPremise sourceHead
          have nextFacts : GeneralPremise.Static.InputFacts environment context.next
              (GeneralPremise.Static.premiseFlow environment.language environment.provider context.rule context.spec
                context.premiseIndex 0 refinement premise).refinement middle :=
            ⟨after.typed,after.canonical,by simpa only [depthZero] using after.represented⟩
          obtain ⟨final,history,sourceTail,completed⟩ := tailIH (context := context.next)
            (fun later member => shapes later (List.mem_cons_of_mem _ member)) tailLocations rfl specification
            contextUnique nextFacts next ordinarySupported.2 staticSupported.2 tail
          exact ⟨final,event::history,.cons sourceHead sourceTail,completed⟩

#print axioms validation_fromReference_bindings
#print axioms premises_fromReference_bindings


/-- A reference rule witness reconstructs an actual ordinary typed scoped
root firing. Source matching, premise readback, reduct totality and target
typing are derived from the actual declaration and captured values. -/
theorem root_fromReference {environment : GeneralPremise.Environment} {rule : RewriteRule}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true)
    (contextUnique : (rule.typeContext.map Prod.fst).Nodup)
    (left : FirstOrder rule.left) (right : FirstOrder rule.right)
    (leftTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (rightTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (shapes : ∀ premise ∈ rule.premises,Validation premise)
    (flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule
      (GeneralRuleBindingInference.inferredSpec rule) = true)
    (static : GeneralPremise.Static.checkRule environment.language environment.provider rule
      (GeneralRuleBindingInference.inferredSpec rule) = true)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (step : ReferenceStep.StepValid relEnv environment.language source (.rule index initial witnesses) target) :
    ∃ trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target := by
  cases step with
  | @rule _ _ actualRule _ final _ actualDeclared matched premises =>
      have sameRule := Option.some.inj (actualDeclared.symm.trans declared)
      subst actualRule
      rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
      have rawMatched : MatchRel rule.left source initial := matchPattern_sound matched
      have initialTyped := matching_captures_typed valid left rawMatched leftTyped
        sourceTyped.1 sourceTyped.2.1 sourceTyped.2.2.1
      have initialDefined := raw_matching_defined left rawMatched
      obtain ⟨captured,matching,compatible⟩ := scoped_instance (initial := []) left (NameCoherent.left rule)
        initialDefined initialTyped contextUnique (by intro _ member; cases member)
      rw [matchRel_correct rawMatched left.isMatchCorrect] at matching
      have capturedTyped := compatible.typed initialTyped contextUnique
      have capturedCanonical := GeneralPremise.matching_canonicalValues GeneralPremise.CanonicalValues.empty
        sourceTyped.2.1 matching
      have facts : GeneralPremise.Static.InputFacts environment
          ⟨index,rule,GeneralRuleBindingInference.inferredSpec rule,bound,0,0⟩
          (GeneralPremise.Static.initialRefinement rule) captured :=
        ⟨capturedTyped,capturedCanonical,GeneralPremise.Static.initialRefinement_holds matching⟩
      have capturedUnique := (matching_unique_names left matching (by simp)).1
      have captures : BindingAgreement rule.left.freeFvarNames captured initial :=
        bindingAgreement_of_scopedCompatible compatible capturedUnique (matchRel_unique_names rawMatched)
          (GeneralPremise.matching_bound_names matching)
          (by
            intro name member
            obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp member
            exact matchRel_names left rawMatched entry stored)
      simp only [GeneralPremise.rulePremisesAdmitted,Bool.and_eq_true] at flow
      simp only [GeneralPremise.Static.checkRule,Bool.and_eq_true] at static
      obtain ⟨completed,history,sourcePremises,completedReadback⟩ := premises_fromReference_bindings relEnv reads valid
        providerClosed (ReferenceStep.captureSites rule) shapes (fun _ _ selected => by simpa using selected)
        rfl rfl contextUnique facts captures flow.1 static.1.1.2 premises
      have completedFacts := facts.afterPremises rfl sourcePremises
      have completedTyped := bindingAgreement_capturesTyped completedFacts.typed completedFacts.canonical
        (inferred_zero _) completedReadback
      have rhsBound : GeneralPremise.BoundNames completed rule.right.freeFvarNames := by
        intro name member
        exact bindingAgreement_available completedReadback name
          (GeneralPremise.namesAvailable_sound _ _ flow.2 name member)
      have rhsDefined : Defined final rule.right.freeFvarNames := by
        intro name member
        apply (lookup_some_iff_mem_names final name).mpr
        exact (completedReadback.ordinaryNames name).mpr
          (GeneralPremise.namesAvailable_sound _ _ flow.2 name member)
      have completedRoots := completedFacts.typed.rootValues (inferred_zero _)
      obtain ⟨actualTarget,read⟩ := instantiation_total
        (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
        right (NameCoherent.right rule) rhsBound completedRoots
        (dependencies_of_typed contextUnique rhsDefined completedTyped)
      have readback := instantiation_readout right completedRoots read
      have sameBindings : applyBindings (ordinary completed) rule.right = applyBindings final rule.right :=
        apply_eq_of_same_lookups right (fun name _ =>
          (ordinary_lookup completed name).trans (completedReadback.lookups name))
      have scopedReadback : Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right =
          applyBindings final rule.right :=
        ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _ (firstOrder_notDeeper _ right)
      have endpoint : actualTarget = Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right :=
        readback.symm.trans (sameBindings.trans scopedReadback.symm)
      have targetTyped : OpenPatternWellSorted environment.language environment.free bound type
          (Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right) := by
        rw [scopedReadback]
        exact substituted_open right rightTyped rhsDefined completedTyped
      obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
      exact ⟨trace,captured,completed,history,.fire declared specified admitted sourceTyped traced capturedTyped
        sourcePremises (read.trans (congrArg some endpoint)) targetTyped⟩

/-- Whole root agreement for the recursive first-order validation domain,
at the original rule ordinal and with the exact original target. -/
theorem root_iff_reference {environment : GeneralPremise.Environment} {rule : RewriteRule}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
      environment.provider = true)
    (noDynamic : environment.provider.dynamicRelations = [])
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index =
      some (GeneralRuleBindingInference.inferredSpec rule))
    (admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true)
    (contextUnique : (rule.typeContext.map Prod.fst).Nodup)
    (left : FirstOrder rule.left) (right : FirstOrder rule.right)
    (leftTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (rightTyped : HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (shapes : ∀ premise ∈ rule.premises,Validation premise)
    (flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule
      (GeneralRuleBindingInference.inferredSpec rule) = true)
    (static : GeneralPremise.Static.checkRule environment.language environment.provider rule
      (GeneralRuleBindingInference.inferredSpec rule) = true)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target) ↔
    ∃ initial witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index initial witnesses) target := by
  constructor
  · rintro ⟨trace,captured,completed,history,fired⟩
    exact root_toReference relEnv reads noDynamic declared specified left right shapes flow fired
  · rintro ⟨initial,witnesses,step⟩
    exact root_fromReference relEnv reads valid providerClosed declared specified admitted contextUnique
      left right leftTyped rightTyped shapes flow static sourceTyped step

#print axioms root_fromReference
#print axioms root_iff_reference


/-- Without directed child calls, the reference premise judgment reads the
provider environment and capture sites, but no language rewrite table. -/
theorem validation_reference_language {first second : LanguageDef} (relEnv : Engine.RelationEnv)
    {premise : Premise} (shape : Validation premise) {sites : Pattern} {bindings result : Bindings}
    {witness : ReferenceStep.Witness}
    (valid : ReferenceStep.PremiseValid relEnv first sites bindings premise witness result) :
    ReferenceStep.PremiseValid relEnv second sites bindings premise witness result := by
  induction shape generalizing sites bindings result witness with
  | query _ _ =>
      cases valid with
      | base accepted member => exact .base accepted member
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | freshness _ =>
      cases valid with
      | base accepted member => exact .base accepted member
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | @quantified collection parameter body bodyShape ih =>
      cases valid with
      | base accepted _ => simp [ReferenceStep.isBase] at accepted
      | step endpoints _ _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
      | @forAll _ _ _ _ _ kind elements bodies selected validated =>
          apply ReferenceStep.PremiseValid.forAll selected
          clear selected
          induction elements generalizing bodies with
          | nil => cases validated; exact .nil
          | cons element elements tailIH =>
              cases validated with
              | cons head tail => exact .cons (ih head) (tailIH tail)

theorem premises_reference_language {first second : LanguageDef} (relEnv : Engine.RelationEnv)
    {premises : List Premise} (shapes : ∀ premise ∈ premises,Validation premise)
    {sites : Pattern} {bindings result : Bindings} {witnesses : List ReferenceStep.Witness}
    (valid : ReferenceStep.PremisesValid relEnv first sites bindings premises witnesses result) :
    ReferenceStep.PremisesValid relEnv second sites bindings premises witnesses result := by
  induction premises generalizing bindings witnesses with
  | nil => cases valid; exact .nil _
  | cons premise premises tailIH =>
      cases valid with
      | cons head tail =>
          exact .cons (validation_reference_language relEnv (shapes premise (List.mem_cons_self ..)) head)
            (tailIH (fun later member => shapes later (List.mem_cons_of_mem _ member)) tail)

#print axioms validation_reference_language
#print axioms premises_reference_language

#print axioms bindingAgreement_of_lookups
#print axioms bindingAgreement_of_scopedCompatible
#print axioms bindingAgreement_available
#print axioms raw_bindParameter_unique
#print axioms raw_bindParameter_names
#print axioms raw_bindParameter_lookup
#print axioms bindingAgreement_bindParameter
#print axioms bindingAgreement_compatible_later
#print axioms arguments_binding_names
#print axioms query_toReference_bindings

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.QuantifiedReference

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.QuantifiedReference

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec MeTTaIL.RuleBinding
open MeTTaIL.ScopedRuleMatching MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted


mutual
/-- A binder-free schema uses every capture at its root depth. -/
theorem binderFree_notDeeper (sites : Pattern) {schema : Pattern} (shape : binderFree schema = true) :
    ReferenceStep.notDeeper sites 0 schema = true := by
  cases schema with
  | fvar name => simp only [ReferenceStep.notDeeper]; split <;> simp
  | bvar => rfl
  | apply label schemas => exact binderFreeList_notDeeper sites shape
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    have children := binderFreeList_notDeeper sites shape
    simp only [ReferenceStep.notDeeper,children,Bool.true_and]
    cases rest with
    | none => rfl
    | some name =>
      change (match captureDepth name 0 sites with
        | some depth => decide (0 ≤ depth)
        | none => true) = true
      cases captureDepth name 0 sites <;> rfl
termination_by sizeOf schema

theorem binderFreeList_notDeeper (sites : Pattern) {schemas : List Pattern}
    (shapes : binderFreeList schemas = true) : ReferenceStep.notDeeperList sites 0 schemas = true := by
  cases schemas with
  | nil => rfl
  | cons head tail =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp shapes
    exact Bool.and_eq_true_iff.mpr ⟨binderFree_notDeeper sites first,binderFreeList_notDeeper sites rest⟩
termination_by sizeOf schemas
end

/-- An ordinary child premise reads a source variable in place; every other
binder-free source reads recursively at depth zero. -/
theorem binderFree_step_readback (sites : Pattern) (bindings : Bindings) {source target : Pattern}
    (shape : binderFree source = true) :
    Match.applyBindingsScoped sites bindings (ReferenceStep.stepDepth sites (.congruence source target))
      source = applyBindings bindings source := by
  cases source with
  | fvar name => exact ReferenceStep.applyBindingsScoped_inPlace_fvar sites bindings name
  | bvar | apply | collection =>
    exact ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings 0 _
      (binderFree_notDeeper sites shape)
  | lambda | multiLambda | subst => simp only [binderFree,Bool.false_eq_true] at shape

/-- The schema predicate is only a primitive shape domain. Its interpretation
must prove that it contains no object-binder or explicit-substitution schemas. -/
class BinderFreeSyntax (Schema : Pattern → Prop) : Prop where
  binderFree : ∀ {schema : Pattern},Schema schema → binderFree schema = true

instance : BinderFreeSyntax FirstOrder := ⟨fun shape => shape.binderFree⟩
instance : BinderFreeSyntax (fun schema => binderFree schema = true) := ⟨fun shape => shape⟩

#print axioms arguments_binding_names_recursive
#print axioms query_toReference_bindings_recursive
#print axioms freshness_readout_recursive
#print axioms binderFree_notDeeper
#print axioms binderFreeList_notDeeper
#print axioms binderFree_step_readback

/-- First-order congruence sources have exact reference readback. A variable
is read at its actual capture depth, while applications are read at depth zero. -/
theorem firstOrder_step_readback (sites : Pattern) (bindings : Bindings) {source target : Pattern}
    (shape : FirstOrder source) :
    Match.applyBindingsScoped sites bindings (ReferenceStep.stepDepth sites (.congruence source target))
      source = applyBindings bindings source := by
  cases shape with
  | metavariable name => exact ReferenceStep.applyBindingsScoped_inPlace_fvar sites bindings name
  | constructor label arguments children =>
      exact ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper sites bindings 0 _
        (firstOrder_notDeeper sites (.constructor label arguments children))

/-- Actual declared schema roles in the caller fibre, together with retained
finite-rest flow, reconstruct a recursive root. The original rule ordinal,
occurrence table, raw witness and exact target are preserved. This does not
assume a whole firing equivalence or constructor-headed left side. -/
theorem root_fromReference_recursive {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    {environment : GeneralPremise.Environment} {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free environment.provider = true)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (contextUnique : (rule.typeContext.map Prod.fst).Nodup)
    (left : Schema rule.left) (right : Schema rule.right)
    (leftTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList rule.typeContext) [] rule.left type)
    (rightTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList rule.typeContext) [] rule.right type)
    (shapes : ∀ premise ∈ rule.premises,ValidationWith Schema premise)
    (inputShapes : ∀ premise ∈ rule.premises,FirstOrderQueryInputs environment.provider premise)
    (flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule spec = true)
    (static : (GeneralPremise.Static.premisesFlow environment.language environment.provider rule spec 0
      (GeneralPremise.Static.initialRefinement rule) rule.premises).supported = true)
    (rests : GeneralPremise.namesAvailable
      (GeneralPremise.Static.premisesFlow environment.language environment.provider rule spec 0
        (GeneralPremise.Static.initialRefinement rule) rule.premises).refinement.finite
      (GeneralPremise.restCaptureNames rule.right) = true)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (step : ReferenceStep.StepValid relEnv environment.language source (.rule index initial witnesses) target) :
    ∃ trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target := by
  cases step with
  | @rule _ _ actualRule _ final _ actualDeclared matched premises =>
    have sameRule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
    have rawMatched : MatchRel rule.left source initial := matchPattern_sound matched
    have rawTyped := matching_recursive_captures_typed valid choices (BinderFreeSyntax.binderFree left)
      rawMatched leftTyped sourceTyped
    have rawUnique := matchRel_unique_names rawMatched
    have dependencies : ∀ name ∈ rule.left.freeFvarNames,dependencies? spec name = some [] := by
      intro name member
      obtain ⟨body,found⟩ := raw_matching_defined_recursive rawMatched name member
      obtain ⟨expected,declared,_⟩ := rawTyped (name,body) (raw_lookup_member found)
      exact dependencies_empty_of_admitted admitted zero declared
    have rawCompatible : Compatible initial initial :=
      fun entry member => bindings_lookup_of_mem rawUnique member
    obtain ⟨captured,matching,compatible⟩ := binderFree_scoped_of_matchRel_admitted (initial := []) admitted
      (BinderFreeSyntax.binderFree left) (NameCoherent.left rule) dependencies rawMatched rawCompatible
      sourceTyped.2.2.2 sourceTyped.2.2.1 (by intro _ member; cases member)
    have capturedTyped : GeneralPremise.TypedAssignment environment ⟨index,rule,spec,bound,0,0⟩ captured :=
      compatible.typed_admitted rawTyped admitted zero
    have capturedCanonical := GeneralPremise.matching_canonicalValues GeneralPremise.CanonicalValues.empty
      sourceTyped.2.1 matching
    have facts : GeneralPremise.Static.InputFacts environment ⟨index,rule,spec,bound,0,0⟩
        (GeneralPremise.Static.initialRefinement rule) captured :=
      ⟨capturedTyped,capturedCanonical,GeneralPremise.Static.initialRefinement_holds matching⟩
    have capturedUnique := (matching_unique_names_recursive matching (by simp)).1
    have captures : BindingAgreement rule.left.freeFvarNames captured initial :=
      bindingAgreement_of_scopedCompatible compatible capturedUnique rawUnique
        (GeneralPremise.matching_bound_names matching)
        (fun name member => (raw_matching_names_recursive rawMatched name).mp member)
    simp only [GeneralPremise.rulePremisesAdmitted,Bool.and_eq_true] at flow
    obtain ⟨completed,history,sourcePremises,completedReadback⟩ :=
      premises_fromReference_bindings_recursive (fun _ shape => BinderFreeSyntax.binderFree shape)
        relEnv reads valid choices providerClosed (ReferenceStep.captureSites rule) shapes
        (fun _ _ selected => by simpa using selected) rfl admitted zero inputShapes contextUnique
        facts captures flow.1 static premises
    have completedFacts := facts.afterPremises rfl sourcePremises
    have rhsBound : GeneralPremise.BoundNames completed rule.right.freeFvarNames := by
      intro name member
      exact bindingAgreement_available completedReadback name
        (GeneralPremise.namesAvailable_sound _ _ flow.2 name member)
    have rhsFinite : GeneralPremise.FiniteCaptureNames completed (GeneralPremise.restCaptureNames rule.right) :=
      fun name member => completedFacts.represented.2.1 name
        (GeneralPremise.namesAvailable_sound _ _ rests name member)
    obtain ⟨actualTarget,read,targetOpen⟩ := binderFree_instantiation_total_open
      (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
      admitted zero completedFacts.typed completedFacts.canonical (BinderFreeSyntax.binderFree right)
      (NameCoherent.right rule) rightTyped rhsBound rhsFinite
    have readback := binderFree_instantiation_readout (BinderFreeSyntax.binderFree right)
      (completedFacts.typed.rootValues zero) read
    have sameBindings : applyBindings (ordinary completed) rule.right = applyBindings final rule.right :=
      applyBindings_eq_of_lookup_agreement _ (fun name _ =>
        (ordinary_lookup completed name).trans (completedReadback.lookups name))
    have scopedReadback : Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right =
        applyBindings final rule.right :=
      ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _
        (binderFree_notDeeper _ (BinderFreeSyntax.binderFree right))
    have endpoint : actualTarget = Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right :=
      readback.symm.trans (sameBindings.trans scopedReadback.symm)
    obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
    exact ⟨trace,captured,completed,history,.fire declared specified admitted sourceTyped traced capturedTyped
      sourcePremises (read.trans (congrArg some endpoint)) (endpoint ▸ targetOpen)⟩

#print axioms root_fromReference_recursive

/-- Directed premise syntax indexed by the declared schema domain, allowing
child steps under arbitrary finite collection quantifiers. -/
inductive DirectedValidationWith (Schema : Pattern → Prop) : Premise → Prop where
  | query {relation : String} {arguments : List Pattern}
      (distinct : relation ≠ "eq") (shapes : ∀ argument ∈ arguments,Schema argument) :
      DirectedValidationWith Schema (.relationQuery relation arguments)
  | freshness {condition : FreshnessCondition} (shape : Schema condition.term) :
      DirectedValidationWith Schema (.freshness condition)
  | step {source target : Pattern} (sourceShape : Schema source) (targetShape : Schema target) :
      DirectedValidationWith Schema (.congruence source target)
  | quantified {collection parameter : String} {body : Premise} (shape : DirectedValidationWith Schema body) :
      DirectedValidationWith Schema (.forAll collection parameter body)

abbrev DirectedValidation := DirectedValidationWith FirstOrder

/-- The directed syntax determines the actual kind and endpoints of a
reference child premise, without changing its derivation witness. -/
theorem DirectedValidationWith.step_shape {Schema : Pattern → Prop} {premise : Premise} {source target : Pattern}
    (shape : DirectedValidationWith Schema premise)
    (endpoints : ReferenceStep.stepEndpoints premise = some (source,target)) :
    premise = .congruence source target ∧ Schema source ∧ Schema target := by
  cases shape with
  | query _ _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | freshness _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | quantified _ => simp [ReferenceStep.stepEndpoints] at endpoints
  | step sourceShape targetShape =>
      simp only [ReferenceStep.stepEndpoints,Option.some.injEq,Prod.mk.injEq] at endpoints
      obtain ⟨rfl,rfl⟩ := endpoints
      exact ⟨rfl,sourceShape,targetShape⟩

theorem DirectedValidation.step_shape {premise : Premise} {source target : Pattern}
    (shape : DirectedValidation premise)
    (endpoints : ReferenceStep.stepEndpoints premise = some (source,target)) :
    premise = .congruence source target ∧ FirstOrder source ∧ FirstOrder target :=
  DirectedValidationWith.step_shape shape endpoints

/-- Row eligibility consists of actual source typing, binding, flow and syntax
facts. No premise or firing agreement is assumed. Constructor heads retain the
sort information absent from an untyped reference rule invocation. -/
structure DirectedRowWith (Schema : Pattern → Prop) (environment : GeneralPremise.Environment) (index : Nat) (rule : RewriteRule) : Prop where
  specified : GeneralPremise.specification? environment index =
    some (GeneralRuleBindingInference.inferredSpec rule)
  admitted : admittedFor rule (GeneralRuleBindingInference.inferredSpec rule) = true
  unique : (rule.typeContext.map Prod.fst).Nodup
  left : Schema rule.left
  right : Schema rule.right
  headed : ∃ label arguments,rule.left = .apply label arguments
  typed : ∃ type,HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.left type ∧
    HasType environment.language (FreeTypeContext.ofList rule.typeContext) [] rule.right type
  premises : ∀ premise ∈ rule.premises,DirectedValidationWith Schema premise
  flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule
    (GeneralRuleBindingInference.inferredSpec rule) = true
  static : GeneralPremise.Static.checkRule environment.language environment.provider rule
    (GeneralRuleBindingInference.inferredSpec rule) = true

abbrev DirectedRow := DirectedRowWith FirstOrder

/-- A source-language profile for literal directed premises. It adds no
admission authority and does not change the language's reference relation. -/
structure DirectedProfileWith (Schema : Pattern → Prop) (environment : GeneralPremise.Environment) : Prop where
  valid : environment.language.validate = []
  providerClosed : GeneralPremise.checkProviderClosed environment.language environment.free
    environment.provider = true
  noDynamic : environment.provider.dynamicRelations = []
  rows : ∀ {index : Nat} {rule : RewriteRule},environment.language.rewrites[index]? = some rule →
    DirectedRowWith Schema environment index rule

abbrev DirectedProfile := DirectedProfileWith FirstOrder


/-- Primitive eligibility for forward source readback. Typing and matching
validity come from the actual firing; no constructor-headed invocation or
reverse source-typing reconstruction is required. -/
structure DirectedForwardRow (Schema : Pattern → Prop) (environment : GeneralPremise.Environment)
    (index : Nat) (rule : RewriteRule) : Prop where
  sourceBindings : ∃ spec,GeneralPremise.specification? environment index = some spec ∧
    GeneralPremise.checkZeroDependencies spec = true ∧
    GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule spec = true
  left : Schema rule.left
  right : Schema rule.right
  premises : ∀ premise ∈ rule.premises,DirectedValidationWith Schema premise

/-- The forward boundary retains only actual declaration/specification,
recursive syntax and binding-flow facts. It does not imply reverse coverage. -/
structure DirectedForwardProfile (Schema : Pattern → Prop) (environment : GeneralPremise.Environment) : Prop where
  noDynamic : environment.provider.dynamicRelations = []
  rows : ∀ {index : Nat} {rule : RewriteRule},environment.language.rewrites[index]? = some rule →
    DirectedForwardRow Schema environment index rule

theorem DirectedProfileWith.forward {Schema : Pattern → Prop} {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) : DirectedForwardProfile Schema environment :=
  ⟨profile.noDynamic,fun selected =>
    let row := profile.rows selected
    ⟨⟨GeneralRuleBindingInference.inferredSpec _,row.specified,inferred_zero _,row.flow⟩,
      row.left,row.right,row.premises⟩⟩

#print axioms DirectedProfileWith.forward

/-- Scoped target matching reconstructs a real literal raw match and merge,
retaining every completed lookup and the exact domain of bound names. -/
theorem step_target_toReference_recursive {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {initial final : Assignment} {target candidate : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {available : List String} {bindings : Bindings}
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (shape : binderFree target = true)
    (typed : GeneralPremise.TypedAssignment environment context final)
    (agreement : BindingAgreement available initial bindings)
    (matched : GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
      (context.site 1) [] 0 initial target candidate trace final) :
    ∃ extension result,extension ∈ matchPattern target candidate ∧ mergeBindings bindings extension = some result ∧
      BindingAgreement (target.freeFvarNames ++ available).eraseDups final result := by
  have matching := matched.matching
  have roots := typed.rootValues zero
  obtain ⟨extension,targetMatched,compatible,extensionUnique,extensionNames⟩ :=
    binderFree_matching_readback shape matching (.refl _) roots
  have before := bindingAgreement_compatible_later agreement matching.extends
  obtain ⟨result,merged,resultCompatible,resultUnique,resultNames⟩ :=
    merge_compatible (ordinary final) bindings extension before compatible agreement.ordinaryUnique
  obtain ⟨finalUnique,finalNames⟩ := matching_unique_names_recursive matching agreement.scopedUnique
  have rawNames : SameNames result (target.freeFvarNames ++ available).eraseDups := by
    intro key
    rw [resultNames key,agreement.ordinaryNames key,extensionNames key,List.mem_eraseDups,List.mem_append]
    exact or_comm
  have completeDomain : SameNames result ((ordinary final).map Prod.fst) := by
    intro key
    rw [ordinary_names,finalNames key,agreement.scopedNames key,rawNames key,
      List.mem_eraseDups,List.mem_append]
    exact or_comm
  have readback := compatible_lookup_all resultCompatible completeDomain
  exact ⟨extension,result,matchRel_complete targetMatched,merged,
    bindingAgreement_of_lookups finalUnique resultUnique rawNames
      (fun key => (ordinary_lookup final key).symm.trans (readback key).symm)⟩

theorem step_target_toReference {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {initial final : Assignment} {target candidate : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {available : List String} {bindings : Bindings}
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (shape : FirstOrder target)
    (typed : GeneralPremise.TypedAssignment environment context final)
    (agreement : BindingAgreement available initial bindings)
    (matched : GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
      (context.site 1) [] 0 initial target candidate trace final) :
    ∃ extension result,extension ∈ matchPattern target candidate ∧ mergeBindings bindings extension = some result ∧
      BindingAgreement (target.freeFvarNames ++ available).eraseDups final result := by
  exact step_target_toReference_recursive (by rw [specification]; exact inferred_zero _) shape.binderFree typed agreement matched

#print axioms firstOrder_step_readback
#print axioms step_target_toReference
#print axioms step_target_toReference_recursive



/-- A premise schema's real occurrence site is coherent at every quantifier depth. -/
theorem nameCoherent_at {rule : RewriteRule} {site : RulePatternSite} {schema : Pattern}
    (located : sitePattern? rule site = some schema) : NameCoherent rule site [] schema := by
  intro suffix
  simp only [List.nil_append,located,Option.bind_some]

theorem Located.step_source {context : GeneralPremise.Context} {source target : Pattern}
    (located : Located context (.congruence source target)) :
    sitePattern? context.rule (context.site 0) = some source := by
  obtain ⟨premise,declared,nested⟩ := Option.bind_eq_some_iff.mp located
  simp only [GeneralPremise.Context.site,sitePattern?,declared,Option.bind_eq_bind,Option.bind_some,nested]
  rfl

theorem Located.step_target {context : GeneralPremise.Context} {source target : Pattern}
    (located : Located context (.congruence source target)) :
    sitePattern? context.rule (context.site 1) = some target := by
  obtain ⟨premise,declared,nested⟩ := Option.bind_eq_some_iff.mp located
  simp only [GeneralPremise.Context.site,sitePattern?,declared,Option.bind_eq_bind,Option.bind_some,nested]
  rfl

/-- Recursive literal reference targets reconstruct actual typed scoped
matches at their authored site. The primitive certificates retain the real
specification, nested rest roles, object/scope conditions and raw merge. -/
theorem step_target_fromReference_recursive {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {initial : Assignment} {target candidate : Pattern}
    {available : List String} {bindings extension result : Bindings} {type : TypeExpr}
    (valid : environment.language.validate = [])
    (choices : CollectionChoiceDeterministic environment.language)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (shape : binderFree target = true)
    (located : sitePattern? context.rule (context.site 1) = some target)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (canonical : GeneralPremise.CanonicalValues initial)
    (agreement : BindingAgreement available initial bindings)
    (schemaTyped : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType environment.language
      (FreeTypeContext.ofList context.rule.typeContext) [] target type)
    (candidateTyped : OpenPatternWellSorted environment.language environment.free context.bound type candidate)
    (matched : extension ∈ matchPattern target candidate)
    (merged : mergeBindings bindings extension = some result) :
    ∃ final trace,GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
      (context.site 1) [] 0 initial target candidate trace final ∧
      GeneralPremise.TypedAssignment environment context final ∧
      BindingAgreement (target.freeFvarNames ++ available).eraseDups final result := by
  have currentTyped := bindingAgreement_capturesTyped typed canonical zero agreement
  have targetMatched : MatchRel target candidate extension := matchPattern_sound matched
  have extensionTyped := matching_recursive_captures_typed valid choices shape targetMatched schemaTyped candidateTyped
  have resultTyped := capturesTyped_merge currentTyped extensionTyped merged
  have resultUnique := mergeBindings_nodup merged agreement.ordinaryUnique
  have before := bindingAgreement_scopedCompatible agreement (typed.rootValues zero)
  have lifted : ScopedCompatible context.bound.length result initial :=
    compatible_lift before (fun _ _ found => merge_lookup_left merged found)
  have targetDefined : Defined result target.freeFvarNames := by
    intro key member
    obtain ⟨body,found⟩ := raw_matching_defined_recursive targetMatched key member
    exact ⟨body,merge_lookup_right merged found⟩
  have dependencies : ∀ key ∈ target.freeFvarNames,dependencies? context.spec key = some [] := by
    intro key member
    obtain ⟨body,found⟩ := targetDefined key member
    obtain ⟨expected,declared,_⟩ := resultTyped (key,body) (raw_lookup_member found)
    exact dependencies_empty_of_admitted admitted zero declared
  have extensionCompatible : Compatible result extension :=
    fun entry member => bindings_lookup_of_mem resultUnique (mergeBindings_right_subset merged member)
  obtain ⟨final,matching,compatible⟩ := binderFree_scoped_of_matchRel_admitted admitted shape
    (nameCoherent_at located) dependencies targetMatched extensionCompatible candidateTyped.2.2.2 candidateTyped.2.2.1 lifted
  have finalTyped : GeneralPremise.TypedAssignment environment context final :=
    compatible.typed_admitted resultTyped admitted zero
  obtain ⟨finalUnique,_⟩ := matching_unique_names_recursive matching agreement.scopedUnique
  have finalBound : GeneralPremise.BoundNames final (target.freeFvarNames ++ available).eraseDups := by
    intro key member
    rw [List.mem_eraseDups,List.mem_append] at member
    rcases member with fromTarget | earlier
    · exact GeneralPremise.matching_bound_names matching key fromTarget
    · obtain ⟨value,found⟩ := bindingAgreement_available agreement key earlier
      exact ⟨value,matching.extends key value found⟩
  have resultNames : ∀ key ∈ result.map Prod.fst,key ∈ (target.freeFvarNames ++ available).eraseDups := by
    intro key member
    obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp member
    rw [List.mem_eraseDups,List.mem_append]
    rcases List.mem_append.mp (merge_members merged stored) with earlier | later
    · exact Or.inr ((agreement.ordinaryNames entry.1).mp (List.mem_map_of_mem earlier))
    · exact Or.inl ((raw_matching_names_recursive targetMatched entry.1).mp (List.mem_map_of_mem later))
  obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  exact ⟨final,trace,traced,finalTyped,
    bindingAgreement_of_scopedCompatible compatible finalUnique resultUnique finalBound resultNames⟩

#print axioms step_target_fromReference_recursive

/-- A literal target match and real raw merge reconstruct the actual scoped
target match at its authored occurrence, with complete binding readback. -/
theorem step_target_fromReference {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {initial : Assignment} {target candidate : Pattern}
    {available : List String} {bindings extension result : Bindings} {type : TypeExpr}
    (valid : environment.language.validate = [])
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (shape : FirstOrder target)
    (located : sitePattern? context.rule (context.site 1) = some target)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (canonical : GeneralPremise.CanonicalValues initial)
    (agreement : BindingAgreement available initial bindings)
    (schemaTyped : HasType environment.language (FreeTypeContext.ofList context.rule.typeContext) [] target type)
    (candidateTyped : OpenPatternWellSorted environment.language environment.free context.bound type candidate)
    (matched : extension ∈ matchPattern target candidate)
    (merged : mergeBindings bindings extension = some result) :
    ∃ final trace,GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
      (context.site 1) [] 0 initial target candidate trace final ∧
      GeneralPremise.TypedAssignment environment context final ∧
      BindingAgreement (target.freeFvarNames ++ available).eraseDups final result := by
  have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
    rw [specification]; exact inferred_zero _
  have currentTyped := bindingAgreement_capturesTyped typed canonical zero agreement
  have targetMatched : MatchRel target candidate extension := matchPattern_sound matched
  have extensionTyped := matching_captures_typed valid shape targetMatched schemaTyped
    candidateTyped.1 candidateTyped.2.1 candidateTyped.2.2.1
  have resultTyped := capturesTyped_merge currentTyped extensionTyped merged
  have before := bindingAgreement_scopedCompatible agreement (typed.rootValues zero)
  have lifted : ScopedCompatible context.bound.length result initial :=
    compatible_lift before (fun _ _ found => merge_lookup_left merged found)
  have targetDefined : Defined result target.freeFvarNames := by
    intro key member
    obtain ⟨body,found⟩ := raw_matching_defined shape targetMatched key member
    exact ⟨body,merge_lookup_right merged found⟩
  obtain ⟨final,matching,compatible⟩ := scoped_instance (initial := initial) shape
    (nameCoherent_at located) targetDefined resultTyped contextUnique lifted
  have targetSame : applyBindings result target = candidate := by
    rw [apply_eq_of_preserved shape (raw_matching_defined shape targetMatched)
      (fun _ _ found => merge_lookup_right merged found)]
    exact matchRel_correct targetMatched shape.isMatchCorrect
  rw [targetSame] at matching
  have finalTyped : GeneralPremise.TypedAssignment environment context final := by
    simpa only [GeneralPremise.TypedAssignment,specification] using compatible.typed resultTyped contextUnique
  obtain ⟨finalUnique,_⟩ := matching_unique_names shape matching agreement.scopedUnique
  have resultUnique := mergeBindings_nodup merged agreement.ordinaryUnique
  have finalBound : GeneralPremise.BoundNames final (target.freeFvarNames ++ available).eraseDups := by
    intro key member
    rw [List.mem_eraseDups,List.mem_append] at member
    rcases member with fromTarget | earlier
    · exact GeneralPremise.matching_bound_names matching key fromTarget
    · obtain ⟨value,found⟩ := bindingAgreement_available agreement key earlier
      exact ⟨value,matching.extends key value found⟩
  have resultNames : ∀ key ∈ result.map Prod.fst,key ∈ (target.freeFvarNames ++ available).eraseDups := by
    intro key member
    obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp member
    rw [List.mem_eraseDups,List.mem_append]
    rcases List.mem_append.mp (merge_members merged stored) with earlier | later
    · exact Or.inr ((agreement.ordinaryNames entry.1).mp (List.mem_map_of_mem earlier))
    · exact Or.inl (matchRel_names shape targetMatched entry later)
  obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  rw [← specification] at traced
  exact ⟨final,trace,traced,finalTyped,
    bindingAgreement_of_scopedCompatible compatible finalUnique resultUnique finalBound resultNames⟩

#print axioms nameCoherent_at
#print axioms Located.step_source
#print axioms Located.step_target
#print axioms step_target_fromReference


open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

mutual
/-- Every literal firing with recursively binder-free schemas has an actual
reference witness, including child and quantified validation derivations. -/
theorem directed_root_toReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedForwardProfile Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index bindings witnesses) target :=
  match fired with
  | .fire (rule := rule) (spec := spec) declared specified _ _ matched capturedTyped held reduct _ => by
      have row := profile.rows declared
      obtain ⟨sourceSpec,sourceSpecified,sourceZero,sourceFlow⟩ := row.sourceBindings
      have sameSpec := Option.some.inj (specified.symm.trans sourceSpecified)
      have zero : GeneralPremise.checkZeroDependencies spec = true := sameSpec.symm ▸ sourceZero
      have roots := capturedTyped.rootValues zero
      obtain ⟨bindings,rawMatched,captures⟩ := binderFree_matching_bindingAgreement
        (BinderFreeSyntax.binderFree row.left) matched.matching roots
      have flow : GeneralPremise.rulePremisesAdmitted environment.language environment.provider rule spec = true :=
        sameSpec.symm ▸ sourceFlow
      simp only [GeneralPremise.rulePremisesAdmitted,Bool.and_eq_true] at flow
      obtain ⟨witnesses,result,premisesValid,completedReadback⟩ := directed_premises_toReference_of_forward
        profile relEnv reads (ReferenceStep.captureSites rule) row.premises zero capturedTyped captures flow.1 held
      have completedRoots := (held.typed capturedTyped).rootValues zero
      have rhs := binderFree_instantiation_readout (BinderFreeSyntax.binderFree row.right) completedRoots reduct
      have ordinaryRhs : applyBindings result rule.right = target :=
        (applyBindings_eq_of_lookup_agreement rule.right (fun key _ =>
          (completedReadback.lookups key).symm.trans (ordinary_lookup completed key).symm)).trans rhs
      have scopedRhs : Match.applyBindingsScoped (ReferenceStep.captureSites rule) result 0 rule.right = target :=
        (ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _
          (binderFree_notDeeper _ (BinderFreeSyntax.binderFree row.right))).trans ordinaryRhs
      rw [← scopedRhs]
      exact ⟨bindings,witnesses,.rule declared
        (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic] using rawMatched) premisesValid⟩
 termination_by structural fired

/-- Ordered premise readback is retained through directed children. -/
theorem directed_premises_toReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedForwardProfile Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {premises : List Premise} {initial final : Assignment}
    {events : List GeneralPremise.Event} {available : List String} {bindings : Bindings}
    (sites : Pattern) (shapes : ∀ premise ∈ premises,DirectedValidationWith Schema premise)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premisesFlow environment.language environment.provider context.rule context.spec
      available premises).supported = true)
    (held : GeneralPremise.PremisesHold environment context premises initial final events) :
    ∃ witnesses result,ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result :=
  match held with
  | .nil => ⟨[],bindings,.nil bindings,agreement⟩
  | .cons head tail => by
      simp only [GeneralPremise.premisesFlow,Bool.and_eq_true] at supported ⊢
      obtain ⟨witness,middle,headValid,next⟩ := directed_premise_toReference_of_forward profile relEnv reads
        (shapes _ (List.mem_cons_self ..)) sites zero typed agreement supported.1 head
      obtain ⟨witnesses,result,tailValid,completed⟩ := directed_premises_toReference_of_forward profile relEnv reads (context := context.next)
        sites (fun later member => shapes later (List.mem_cons_of_mem _ member)) zero
        (head.typed typed) next supported.2 tail
      exact ⟨witness::witnesses,result,.cons headValid tailValid,completed⟩
 termination_by structural held

/-- Actual literal directed premises construct reference evidence by mutual
induction on the actual child derivations, rather than assuming a child bridge. -/
theorem directed_premise_toReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedForwardProfile Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider) {premise : Premise}
    (shape : DirectedValidationWith Schema premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial final : Assignment} {event : GeneralPremise.Event}
    {available : List String} {bindings : Bindings}
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      available premise).supported = true)
    (held : GeneralPremise.PremiseHolds environment context premise initial final event) :
    ∃ witness result,ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result :=
  match held with
  | .query query => by
      cases shape with
      | query distinct schemas =>
          obtain ⟨result,member,next⟩ := query_toReference_bindings_recursive relEnv reads profile.noDynamic zero
            (binderFreeList_of_members (fun schema member => BinderFreeSyntax.binderFree (schemas schema member))) agreement supported query
          exact ⟨.base result,result,.base rfl member,next⟩
  | .freshness (condition := condition) (atom := atom) (subject := subject) read fresh => by
      cases shape with
      | freshness subjectShape =>
          have roots := typed.rootValues zero
          obtain ⟨named,subjectRead⟩ := freshness_readout_recursive
            (BinderFreeSyntax.binderFree subjectShape) roots read
          have lookups : ∀ name,(ordinary initial).lookup name = bindings.lookup name :=
            fun name => (ordinary_lookup initial name).trans (agreement.lookups name)
          have rawNamed : resolveFreshVarName bindings condition.varName = some atom := by
            unfold resolveFreshVarName at named ⊢
            rw [← lookups]
            exact named
          have rawSubject : applyBindings bindings condition.term = subject :=
            (applyBindings_eq_of_lookup_agreement _ (fun name _ => (lookups name).symm)).trans subjectRead
          have member : bindings ∈ Engine.premiseStepWithEnv relEnv environment.language bindings (.freshness condition) := by
            simp only [Engine.premiseStepWithEnv,rawNamed,rawSubject]
            rw [if_pos (show Substitution.checkFreshness ⟨atom,subject⟩ = true from
              (GeneralPremise.syntactic_freshness_iff _ _).mpr fresh)]
            exact List.mem_singleton_self _
          exact ⟨.base bindings,bindings,.base rfl member,agreement⟩
  | .step (source := source) (target := target) (actualSource := actualSource)
      _ instantiated child targetMatched finalTyped => by
      cases shape with
      | step sourceShape targetShape =>
          have roots := typed.rootValues zero
          have sourceRead : applyBindings (ordinary initial) source = actualSource := by
            exact binderFree_instantiation_readout (BinderFreeSyntax.binderFree sourceShape) roots instantiated
          have rawSource : applyBindings bindings source = actualSource :=
            (applyBindings_eq_of_lookup_agreement source (fun key _ =>
              (agreement.lookups key).symm.trans (ordinary_lookup initial key).symm)).trans sourceRead
          obtain ⟨childBindings,childWitnesses,childValid⟩ := directed_root_toReference_of_forward profile relEnv reads child
          have scopedSource := (binderFree_step_readback sites bindings (target := target) (BinderFreeSyntax.binderFree sourceShape)).trans rawSource
          rw [← scopedSource] at childValid
          obtain ⟨extension,result,targetRaw,merged,next⟩ := step_target_toReference_recursive zero (BinderFreeSyntax.binderFree targetShape)
            finalTyped agreement targetMatched
          exact ⟨_,result,.step rfl childValid targetRaw merged,next⟩
  | .scopedStep _ _ _ _ => by cases shape
  | .quantified (collection := collection) (parameter := parameter) (body := body) read validated => by
      cases shape with
      | quantified bodyShape =>
          have finalEq := validated.final_eq_initial
          have roots := typed.rootValues zero
          have carrier : bindings.lookup _ = some (.collection _ _ none) :=
            ((ordinary_lookup initial _).trans (agreement.lookups _)).symm.trans
              (finiteCollection_lookup roots read)
          have localSupported : (GeneralPremise.premiseFlow environment.language environment.provider
              context.rule context.spec (parameter::available) body).supported = true := by
            have parts := supported
            simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at parts
            exact parts.2
          obtain ⟨witnesses,bodiesValid⟩ := directed_elements_toReference_of_forward profile relEnv reads bodyShape
            sites zero agreement localSupported validated
          exact ⟨.forAll witnesses,bindings,.forAll carrier bodiesValid,by
            simpa only [GeneralPremise.premiseFlow,finalEq] using agreement⟩
 termination_by structural held

/-- Each quantified child premise is replayed against the same enclosing
bindings, retaining the original element order. -/
theorem directed_elements_toReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedForwardProfile Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {body : Premise} {parameter : String} {ordinal : Nat}
    {items : List Pattern} {initial final : Assignment} {events : List (Nat × Pattern × List GeneralPremise.Event)}
    {available : List String} {bindings : Bindings}
    (shape : DirectedValidationWith Schema body) (sites : Pattern)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      (parameter::available) body).supported = true)
    (held : GeneralPremise.QuantifiedElements environment context parameter body ordinal items initial final events) :
    ∃ witnesses,ReferenceStep.ForAllValid relEnv environment.language sites bindings parameter body items witnesses :=
  match held with
  | .nil => ⟨[],.nil⟩
  | .cons localTyped bodyHeld tail => by
      obtain ⟨witness,result,bodyValid,_⟩ := directed_premise_toReference_of_forward profile relEnv reads (context := context.quantified) shape sites
        zero localTyped (bindingAgreement_bindParameter agreement parameter context.bound _)
        supported bodyHeld
      obtain ⟨witnesses,tailValid⟩ := directed_elements_toReference_of_forward profile relEnv reads shape sites zero
        agreement supported tail
      exact ⟨witness::witnesses,.cons bodyValid tailValid⟩
 termination_by structural held
end


/-- Literal source soundness for the existing root relation, with the actual
rule ordinal and complete premise witness produced by the shared induction. -/
theorem directed_step_toReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    {environment : GeneralPremise.Environment} (profile : DirectedForwardProfile Schema environment)
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (fired : ∃ index trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ReferenceStep.Step relEnv environment.language source target := by
  obtain ⟨index,trace,captured,completed,history,fired⟩ := fired
  obtain ⟨bindings,witnesses,valid⟩ := directed_root_toReference_of_forward profile relEnv reads fired
  exact ⟨.rule index bindings witnesses,valid⟩

#print axioms directed_step_toReference_of_forward


theorem directed_root_toReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index bindings witnesses) target :=
  directed_root_toReference_of_forward profile.forward relEnv reads fired


theorem directed_premises_toReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {premises : List Premise} {initial final : Assignment}
    {events : List GeneralPremise.Event} {available : List String} {bindings : Bindings}
    (sites : Pattern) (shapes : ∀ premise ∈ premises,DirectedValidationWith Schema premise)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premisesFlow environment.language environment.provider context.rule context.spec
      available premises).supported = true)
    (held : GeneralPremise.PremisesHold environment context premises initial final events) :
    ∃ witnesses result,ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result :=
  directed_premises_toReference_of_forward profile.forward relEnv reads sites shapes (by rw [specification]; exact inferred_zero _) typed agreement supported held


theorem directed_premise_toReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider) {premise : Premise}
    (shape : DirectedValidationWith Schema premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial final : Assignment} {event : GeneralPremise.Event}
    {available : List String} {bindings : Bindings}
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (typed : GeneralPremise.TypedAssignment environment context initial)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      available premise).supported = true)
    (held : GeneralPremise.PremiseHolds environment context premise initial final event) :
    ∃ witness result,ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result :=
  directed_premise_toReference_of_forward profile.forward relEnv reads shape sites (by rw [specification]; exact inferred_zero _) typed agreement supported held


theorem directed_elements_toReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {body : Premise} {parameter : String} {ordinal : Nat}
    {items : List Pattern} {initial final : Assignment} {events : List (Nat × Pattern × List GeneralPremise.Event)}
    {available : List String} {bindings : Bindings}
    (shape : DirectedValidationWith Schema body) (sites : Pattern)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (agreement : BindingAgreement available initial bindings)
    (supported : (GeneralPremise.premiseFlow environment.language environment.provider context.rule context.spec
      (parameter::available) body).supported = true)
    (held : GeneralPremise.QuantifiedElements environment context parameter body ordinal items initial final events) :
    ∃ witnesses,ReferenceStep.ForAllValid relEnv environment.language sites bindings parameter body items witnesses :=
  directed_elements_toReference_of_forward profile.forward relEnv reads shape sites (by rw [specification]; exact inferred_zero _) agreement supported held


theorem directed_step_toReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    {environment : GeneralPremise.Environment} (profile : DirectedProfileWith Schema environment)
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv environment.provider)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (fired : ∃ index trace captured completed history,
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ReferenceStep.Step relEnv environment.language source target :=
  directed_step_toReference_of_forward profile.forward relEnv reads fired

#print axioms directed_root_toReference_of_forward
#print axioms directed_premises_toReference_of_forward
#print axioms directed_premise_toReference_of_forward
#print axioms directed_elements_toReference_of_forward
#print axioms directed_step_toReference_of_forward

#print axioms directed_root_toReference
#print axioms directed_premises_toReference
#print axioms directed_premise_toReference
#print axioms directed_elements_toReference

mutual
/-- Independent reference rule witnesses reconstruct actual typed roots.
The witness's original rule ordinal is retained, and target typing is earned
from the declared rule and reconstructed completed bindings. -/
theorem directed_root_fromReference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {source target : Pattern} {witness : ReferenceStep.Witness}
    {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (step : ReferenceStep.StepValid relEnv environment.language source witness target) :
    ∃ index initial witnesses trace captured completed history,
      witness = .rule index initial witnesses ∧
      GeneralPremise.RootFiring environment bound type source index trace captured completed history target :=
  match step with
  | .rule (index := index) (rule := rule) (initial := initial) (final := final) declared matched premises => by
      have row := profile.rows declared
      rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
      have rawMatched : MatchRel rule.left source initial := matchPattern_sound matched
      have leftSource := matchRel_correct rawMatched row.left.isMatchCorrect
      obtain ⟨label,arguments,headed⟩ := row.headed
      obtain ⟨ruleType,leftTyped,rightTyped⟩ := row.typed
      have sameType : ruleType = type := by
        have sourceHas := sourceTyped.1
        rw [← leftSource,headed] at sourceHas
        rw [headed] at leftTyped
        simp only [applyBindings] at sourceHas
        exact apply_types_agree profile.valid leftTyped sourceHas
      subst ruleType
      have initialTyped := matching_captures_typed profile.valid row.left rawMatched leftTyped
        sourceTyped.1 sourceTyped.2.1 sourceTyped.2.2.1
      have initialDefined := raw_matching_defined row.left rawMatched
      obtain ⟨captured,matching,compatible⟩ := scoped_instance (initial := []) row.left (NameCoherent.left rule)
        initialDefined initialTyped row.unique (by intro _ member; cases member)
      rw [leftSource] at matching
      have capturedTyped := compatible.typed initialTyped row.unique
      have capturedCanonical := GeneralPremise.matching_canonicalValues GeneralPremise.CanonicalValues.empty
        sourceTyped.2.1 matching
      have facts : GeneralPremise.Static.InputFacts environment
          ⟨index,rule,GeneralRuleBindingInference.inferredSpec rule,bound,0,0⟩
          (GeneralPremise.Static.initialRefinement rule) captured :=
        ⟨capturedTyped,capturedCanonical,GeneralPremise.Static.initialRefinement_holds matching⟩
      have capturedUnique := (matching_unique_names row.left matching (by simp)).1
      have captures : BindingAgreement rule.left.freeFvarNames captured initial :=
        bindingAgreement_of_scopedCompatible compatible capturedUnique (matchRel_unique_names rawMatched)
          (GeneralPremise.matching_bound_names matching)
          (by
            intro key member
            obtain ⟨entry,stored,rfl⟩ := List.mem_map.mp member
            exact matchRel_names row.left rawMatched entry stored)
      have flow := row.flow
      have static := row.static
      simp only [GeneralPremise.rulePremisesAdmitted,Bool.and_eq_true] at flow
      simp only [GeneralPremise.Static.checkRule,Bool.and_eq_true] at static
      obtain ⟨completed,history,sourcePremises,completedReadback⟩ := directed_premises_fromReference profile
        relEnv reads (ReferenceStep.captureSites rule) row.premises
        (fun _ _ selected => by simpa using selected) rfl rfl row.unique facts captures flow.1 static.1.1.2 premises
      have completedFacts := facts.afterPremises rfl sourcePremises
      have completedTyped := bindingAgreement_capturesTyped completedFacts.typed completedFacts.canonical
        (inferred_zero _) completedReadback
      have rhsBound : GeneralPremise.BoundNames completed rule.right.freeFvarNames := by
        intro key member
        exact bindingAgreement_available completedReadback key
          (GeneralPremise.namesAvailable_sound _ _ flow.2 key member)
      have rhsDefined : Defined final rule.right.freeFvarNames := by
        intro key member
        apply (lookup_some_iff_mem_names final key).mpr
        exact (completedReadback.ordinaryNames key).mpr
          (GeneralPremise.namesAvailable_sound _ _ flow.2 key member)
      have completedRoots := completedFacts.typed.rootValues (inferred_zero _)
      obtain ⟨actualTarget,read⟩ := instantiation_total
        (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
        row.right (NameCoherent.right rule) rhsBound completedRoots
        (dependencies_of_typed row.unique rhsDefined completedTyped)
      have readback := instantiation_readout row.right completedRoots read
      have sameBindings : applyBindings (ordinary completed) rule.right = applyBindings final rule.right :=
        apply_eq_of_same_lookups row.right (fun key _ =>
          (ordinary_lookup completed key).trans (completedReadback.lookups key))
      have scopedReadback : Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right =
          applyBindings final rule.right :=
        ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _
          (firstOrder_notDeeper _ row.right)
      have endpoint : actualTarget = Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right :=
        readback.symm.trans (sameBindings.trans scopedReadback.symm)
      have targetTyped : OpenPatternWellSorted environment.language environment.free bound type
          (Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right) := by
        rw [scopedReadback]
        exact substituted_open row.right rightTyped rhsDefined completedTyped
      obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
      exact ⟨_,initial,_,trace,captured,completed,history,rfl,
        .fire declared row.specified row.admitted sourceTyped traced capturedTyped sourcePremises
          (read.trans (congrArg some endpoint)) targetTyped⟩
 termination_by sizeOf witness
 decreasing_by all_goals simp_wf

/-- Original reference premise lists reconstruct ordered actual histories
and complete binding readback, with the original rule occurrences. -/
theorem directed_premises_fromReference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {premises : List Premise} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings}
    {witnesses : List ReferenceStep.Witness} (sites : Pattern)
    (shapes : ∀ premise ∈ premises,DirectedValidation premise)
    (locations : ∀ offset premise,premises[offset]? = some premise →
      context.rule.premises[context.premiseIndex + offset]? = some premise)
    (depthZero : context.quantifierDepth = 0)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (ordinarySupported : (GeneralPremise.premisesFlow environment.language environment.provider
      context.rule context.spec available premises).supported = true)
    (staticSupported : (GeneralPremise.Static.premisesFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex refinement premises).supported = true)
    (held : ReferenceStep.PremisesValid relEnv environment.language sites bindings premises witnesses result) :
    ∃ final history,GeneralPremise.PremisesHold environment context premises initial final history ∧
      BindingAgreement (GeneralPremise.premisesFlow environment.language environment.provider
        context.rule context.spec available premises).available final result :=
  match held with
  | .nil _ => ⟨initial,[],.nil,agreement⟩
  | .cons (premise := premise) (premises := premises) head tail => by
      simp only [GeneralPremise.premisesFlow,Bool.and_eq_true] at ordinarySupported
      simp only [GeneralPremise.Static.premisesFlow,Bool.and_eq_true] at staticSupported
      have here : context.rule.premises[context.premiseIndex]? = some premise := by
        simpa only [Nat.add_zero] using locations 0 premise rfl
      have located : Located context premise := by
        simp only [Located,here,depthZero,Option.bind_some,quantifiedBody?]
      have headStatic : (GeneralPremise.Static.premiseFlow environment.language environment.provider
          context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported = true :=
        by simpa only [depthZero] using staticSupported.1
      obtain ⟨middle,event,sourceHead,next⟩ := directed_premise_fromReference profile relEnv reads
        (shapes premise (List.mem_cons_self ..)) sites specification contextUnique facts agreement located
        ordinarySupported.1 headStatic head
      have tailLocations : ∀ offset later,premises[offset]? = some later →
          context.next.rule.premises[context.next.premiseIndex + offset]? = some later := by
        intro offset later selected
        simpa only [GeneralPremise.Context.next,Nat.add_assoc,Nat.add_comm 1 offset]
          using locations (offset + 1) later selected
      have after := facts.afterPremise sourceHead
      have nextFacts : GeneralPremise.Static.InputFacts environment context.next
          (GeneralPremise.Static.premiseFlow environment.language environment.provider context.rule context.spec
            context.premiseIndex 0 refinement premise).refinement middle :=
        ⟨after.typed,after.canonical,by simpa only [depthZero] using after.represented⟩
      obtain ⟨final,history,sourceTail,completed⟩ := directed_premises_fromReference profile relEnv reads
        (context := context.next) sites (fun later member => shapes later (List.mem_cons_of_mem _ member))
        tailLocations rfl specification contextUnique nextFacts next ordinarySupported.2 staticSupported.2 tail
      exact ⟨final,event::history,.cons sourceHead sourceTail,completed⟩
 termination_by sizeOf witnesses
 decreasing_by all_goals simp_wf; all_goals omega

/-- Literal directed source premises reconstruct their actual retained
children. Local quantifier depths and typed source endpoints are derived. -/
theorem directed_premise_fromReference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {premise : Premise} (shape : DirectedValidation premise) (sites : Pattern)
    {context : GeneralPremise.Context} {initial : Assignment} {available : List String}
    {refinement : GeneralPremise.Static.Refinement} {bindings result : Bindings} {witness : ReferenceStep.Witness}
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (located : Located context premise)
    (ordinarySupported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec available premise).supported = true)
    (staticSupported : (GeneralPremise.Static.premiseFlow environment.language environment.provider
      context.rule context.spec context.premiseIndex context.quantifierDepth refinement premise).supported = true)
    (held : ReferenceStep.PremiseValid relEnv environment.language sites bindings premise witness result) :
    ∃ final event,GeneralPremise.PremiseHolds environment context premise initial final event ∧
      BindingAgreement (GeneralPremise.premiseFlow environment.language environment.provider
        context.rule context.spec available premise).available final result :=
  match held with
  | .base isBase member => by
      cases shape with
      | query distinct schemas =>
          exact validation_fromReference_bindings relEnv reads profile.valid profile.providerClosed
            (.query distinct schemas) sites specification contextUnique facts agreement located
            ordinarySupported staticSupported (.base isBase member)
      | freshness termShape =>
          exact validation_fromReference_bindings relEnv reads profile.valid profile.providerClosed
            (.freshness termShape) sites specification contextUnique facts agreement located
            ordinarySupported staticSupported (.base isBase member)
      | step _ _ => simp [ReferenceStep.isBase] at isBase
      | quantified _ => simp [ReferenceStep.isBase] at isBase
  | .step (source := source) (target := target) (candidate := candidate) endpoints child matched merged => by
      obtain ⟨samePremise,sourceShape,targetShape⟩ := shape.step_shape endpoints
      have stepLocated : Located context (.congruence source target) := samePremise ▸ located
      have stepStatic : (GeneralPremise.Static.premiseFlow environment.language environment.provider
          context.rule context.spec context.premiseIndex context.quantifierDepth refinement
          (.congruence source target)).supported = true := samePremise ▸ staticSupported
      have checked := ordinarySupported
      rw [samePremise] at checked
      simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at checked
      obtain ⟨sourceAvailable,sortChecked⟩ := checked
      cases sourceFound : GeneralPremise.sourceType? environment.language context.rule source with
      | none => simp [sourceFound] at sortChecked
      | some childType =>
          simp only [sourceFound] at sortChecked
          have schemaTypes := GeneralPremise.schemaValuesChecked_sound sortChecked
          rw [lookupRuleType_eq] at schemaTypes
          obtain ⟨sourceTyped,targetTyped⟩ :
              HasType environment.language (FreeTypeContext.ofList context.rule.typeContext) [] source childType ∧
              HasType environment.language (FreeTypeContext.ofList context.rule.typeContext) [] target childType := by
            cases schemaTypes with
            | cons sourceTyped tail => cases tail with | cons targetTyped _ => exact ⟨sourceTyped,targetTyped⟩
          have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
            rw [specification]; exact inferred_zero _
          have currentTyped := bindingAgreement_capturesTyped facts.typed facts.canonical zero agreement
          have roots := facts.typed.rootValues zero
          have sourceBound : GeneralPremise.BoundNames initial source.freeFvarNames :=
            fun key member => bindingAgreement_available agreement key
              (GeneralPremise.namesAvailable_sound _ _ sourceAvailable key member)
          have sourceDefined : Defined bindings source.freeFvarNames := compatible_defined
            (bindingAgreement_scopedCompatible agreement roots) sourceBound
          obtain ⟨actualSource,instantiated⟩ := instantiation_total
            (operation := Substitution.instantiateBVar) sourceShape (nameCoherent_at stepLocated.step_source)
            sourceBound roots (dependencies_of_typed contextUnique sourceDefined currentTyped)
          have scopedInstantiation : instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source = some actualSource := by
            rw [specification]; exact instantiated
          have sourceRead := instantiation_readout sourceShape roots instantiated
          have rawSource : applyBindings bindings source = actualSource :=
            (apply_eq_of_same_lookups sourceShape (fun key _ =>
              (agreement.lookups key).symm.trans (ordinary_lookup initial key).symm)).trans sourceRead
          have referenceSource : Match.applyBindingsScoped sites bindings
              (ReferenceStep.stepDepth sites premise) source = actualSource :=
            (congrArg (fun current => Match.applyBindingsScoped sites bindings
              (ReferenceStep.stepDepth sites current) source) samePremise).trans
                ((firstOrder_step_readback sites bindings (target := target) sourceShape).trans rawSource)
          have childTyped := GeneralPremise.Static.step_source_typed facts zero stepStatic sourceFound
            scopedInstantiation
          have referenceTyped : OpenPatternWellSorted environment.language environment.free context.bound
              childType (Match.applyBindingsScoped sites bindings
                (ReferenceStep.stepDepth sites premise) source) :=
            referenceSource.symm ▸ childTyped
          obtain ⟨childIndex,childInitial,childWitnesses,childTrace,childCaptured,childCompleted,childHistory,
            _,childFired⟩ := directed_root_fromReference profile relEnv reads referenceTyped child
          have candidateTyped : OpenPatternWellSorted environment.language environment.free context.bound
              childType candidate := by
            cases childFired with
            | fire _ _ _ _ _ _ _ _ sorted => exact sorted
          obtain ⟨final,targetTrace,targetMatched,finalTyped,next⟩ := step_target_fromReference profile.valid
            specification contextUnique targetShape stepLocated.step_target facts.typed facts.canonical agreement
            targetTyped candidateTyped matched merged
          rw [referenceSource] at childFired
          have interpreted : GeneralPremise.PremiseHolds environment context (.congruence source target)
              initial final _ := .step sourceFound scopedInstantiation childFired targetMatched finalTyped
          exact ⟨final,_,samePremise.symm ▸ interpreted,by simpa only [samePremise,GeneralPremise.premiseFlow] using next⟩
  | .forAll (collection := collection) (parameter := parameter) (body := body)
      (kind := kind) (elements := elements) selected bodies => by
      cases shape with
      | quantified bodyShape =>
          have zero : GeneralPremise.checkZeroDependencies context.spec = true := by
            rw [specification]; exact inferred_zero _
          have read : GeneralPremise.finiteCollection? context.bound.length initial collection =
              some (kind,elements) := by
            rw [finiteCollection_readout (facts.typed.rootValues zero),ordinary_lookup,agreement.lookups,selected]
            rfl
          simp only [GeneralPremise.Static.premiseFlow,Bool.and_eq_true] at staticSupported
          split at staticSupported <;> try simp at staticSupported
          rename_i declaredKind elementType parameterType collectionDeclared parameterDeclared
          have typeSame := staticSupported.1.2.1
          subst parameterType
          have parameterDependencies := staticSupported.1.2.2
          have localStatic := staticSupported.2
          have localOrdinary : (GeneralPremise.premiseFlow environment.language environment.provider
              context.rule context.spec (parameter::available) body).supported = true := by
            have parts := ordinarySupported
            simp only [GeneralPremise.premiseFlow,Bool.and_eq_true] at parts
            exact parts.2
          obtain ⟨elementsTyped,objects⟩ := GeneralPremise.finiteCollection_elements_typed
            facts.typed zero collectionDeclared read
          have canonical := GeneralPremise.finiteCollection?_canonical facts.canonical read
          obtain ⟨events,sourceElements⟩ := directed_elements_fromReference profile relEnv reads bodyShape sites
            specification contextUnique facts agreement located.quantified parameterDeclared parameterDependencies
            localOrdinary localStatic elementsTyped objects canonical bodies
          exact ⟨initial,_,.quantified read sourceElements,agreement⟩
 termination_by sizeOf witness
 decreasing_by all_goals simp_wf; all_goals omega

/-- Reference bodies reconstruct local typed continuations without exporting
local output bindings to another element or to the enclosing rule. -/
theorem directed_elements_fromReference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {context : GeneralPremise.Context} {body : Premise} {parameter : String} {items : List Pattern}
    {initial : Assignment} {available : List String} {bindings : Bindings}
    {refinement : GeneralPremise.Static.Refinement} {proofs : List ReferenceStep.Witness}
    {elementType : TypeExpr} {ordinal : Nat}
    (shape : DirectedValidation body) (sites : Pattern)
    (specification : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    (contextUnique : (context.rule.typeContext.map Prod.fst).Nodup)
    (facts : GeneralPremise.Static.InputFacts environment context refinement initial)
    (agreement : BindingAgreement available initial bindings)
    (located : Located context.quantified body)
    (parameterDeclared : GeneralPremise.lookupRuleType? context.rule parameter = some elementType)
    (parameterDependencies : dependencies? context.spec parameter = some [])
    (ordinarySupported : (GeneralPremise.premiseFlow environment.language environment.provider
      context.rule context.spec (parameter::available) body).supported = true)
    (staticSupported : (GeneralPremise.Static.premiseFlow environment.language environment.provider context.rule
      context.spec context.premiseIndex (context.quantifierDepth + 1)
      (GeneralPremise.Static.localRefinement refinement parameter) body).supported = true)
    (elementsTyped : ElementsHaveType environment.language environment.free context.bound items elementType)
    (objects : isObjectPatternList items = true) (canonical : Pattern.hasCanonicalBinderMetadataList items = true)
    (held : ReferenceStep.ForAllValid relEnv environment.language sites bindings parameter body items proofs) :
    ∃ events,GeneralPremise.QuantifiedElements environment context parameter body ordinal items initial initial events :=
  match held with
  | .nil => ⟨[],.nil⟩
  | .cons bodyValid tail => by
      cases elementsTyped with
      | cons elementTyped tailTyped =>
          simp only [isObjectPatternList,Bool.and_eq_true] at objects
          simp only [Pattern.hasCanonicalBinderMetadataList,Bool.and_eq_true] at canonical
          have localTyped := facts.typed.bindParameter parameterDeclared parameterDependencies elementTyped objects.1
          have localFacts : GeneralPremise.Static.InputFacts environment context.quantified
              (GeneralPremise.Static.localRefinement refinement parameter)
              (GeneralPremise.bindParameter parameter (GeneralPremise.localValue context.bound _) initial) :=
            ⟨localTyped,facts.canonical.bindParameter parameter canonical.1,
              facts.represented.bindParameter parameter _⟩
          obtain ⟨localFinal,event,sourceBody,_⟩ := directed_premise_fromReference profile relEnv reads
            (context := context.quantified) shape sites specification contextUnique localFacts
            (bindingAgreement_bindParameter agreement parameter context.bound _) located ordinarySupported staticSupported
            bodyValid
          obtain ⟨events,sourceTail⟩ := directed_elements_fromReference profile relEnv reads (ordinal := ordinal + 1)
            shape sites specification contextUnique facts agreement located parameterDeclared parameterDependencies
            ordinarySupported staticSupported tailTyped objects.2 canonical.2 tail
          exact ⟨(ordinal,_,[event])::events,.cons localTyped sourceBody sourceTail⟩
 termination_by sizeOf proofs
 decreasing_by all_goals simp_wf; all_goals omega
end

#print axioms directed_root_fromReference
#print axioms directed_premises_fromReference
#print axioms directed_premise_fromReference
#print axioms directed_elements_fromReference

/-- Exact root agreement for directed literal first-order premises,
including children nested under collection quantifiers. -/
theorem directed_root_iff_reference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {source target : Pattern} {index : Nat} {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ trace captured completed history,GeneralPremise.RootFiring environment bound type source index
      trace captured completed history target) ↔
    ∃ initial witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index initial witnesses) target := by
  constructor
  · rintro ⟨trace,captured,completed,history,fired⟩
    exact directed_root_toReference profile relEnv reads fired
  · rintro ⟨initial,witnesses,step⟩
    obtain ⟨actualIndex,_,_,trace,captured,completed,history,ordinal,fired⟩ :=
      directed_root_fromReference profile relEnv reads sourceTyped step
    have sameIndex := (ReferenceStep.Witness.rule.inj ordinal).1
    subst actualIndex
    exact ⟨trace,captured,completed,history,fired⟩

/-- Existence of an actual typed root agrees with the original literal
reference step; no equation quotient or contextual descent is added. -/
theorem directed_step_iff_reference {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    {source target : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ index trace captured completed history,GeneralPremise.RootFiring environment bound type source index
      trace captured completed history target) ↔ ReferenceStep.Step relEnv environment.language source target := by
  constructor
  · rintro ⟨index,trace,captured,completed,history,fired⟩
    obtain ⟨initial,witnesses,step⟩ := directed_root_toReference profile relEnv reads fired
    exact ⟨.rule index initial witnesses,step⟩
  · rintro ⟨witness,step⟩
    obtain ⟨index,_,_,trace,captured,completed,history,_,fired⟩ :=
      directed_root_fromReference profile relEnv reads sourceTyped step
    exact ⟨index,trace,captured,completed,history,fired⟩

#print axioms directed_root_iff_reference
#print axioms directed_step_iff_reference

mutual
/-- The existing reference witness is invariant under real rule annotation
changes that preserve the indexed left, right and premise fields. -/
theorem reference_step_same_core {first second : LanguageDef}
    (sameCore : first.rewrites.map ruleCore = second.rewrites.map ruleCore)
    (relEnv : Engine.RelationEnv) {source target : Pattern} {witness : ReferenceStep.Witness}
    (step : ReferenceStep.StepValid relEnv first source witness target) :
    ReferenceStep.StepValid relEnv second source witness target :=
  match step with
  | .rule (index := index) (rule := rule) (initial := initial) (final := final)
      declared matched premises => by
      have selected : (second.rewrites[index]?).map ruleCore = some (ruleCore rule) := by
        rw [← List.getElem?_map,sameCore.symm,List.getElem?_map,declared]
        rfl
      obtain ⟨other,otherDeclared,coreEqual⟩ := Option.map_eq_some_iff.mp selected
      simp only [ruleCore,Prod.mk.injEq] at coreEqual
      obtain ⟨leftEqual,rightEqual,premisesEqual⟩ := coreEqual
      have sitesEqual : ReferenceStep.captureSites other = ReferenceStep.captureSites rule := by
        simp only [ReferenceStep.captureSites,leftEqual,premisesEqual]
      have transformed := reference_premises_same_core sameCore relEnv premises
      rw [← sitesEqual,← premisesEqual] at transformed
      have otherMatched : initial ∈ ReflectiveCanonical.matchPatternForRule second other source := by
        simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,leftEqual] using matched
      have endpoint : Match.applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right =
          Match.applyBindingsScoped (ReferenceStep.captureSites other) final 0 other.right := by
        rw [sitesEqual,rightEqual]
      rw [endpoint]
      exact .rule otherDeclared otherMatched transformed
 termination_by sizeOf witness
 decreasing_by all_goals simp_wf

/-- Premise-list transport keeps exact witnesses and completed bindings. -/
theorem reference_premises_same_core {first second : LanguageDef}
    (sameCore : first.rewrites.map ruleCore = second.rewrites.map ruleCore)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {initial final : Bindings}
    {premises : List Premise} {witnesses : List ReferenceStep.Witness}
    (held : ReferenceStep.PremisesValid relEnv first sites initial premises witnesses final) :
    ReferenceStep.PremisesValid relEnv second sites initial premises witnesses final :=
  match held with
  | .nil bindings => .nil bindings
  | .cons head tail => .cons (reference_premise_same_core sameCore relEnv head)
      (reference_premises_same_core sameCore relEnv tail)
 termination_by sizeOf witnesses
 decreasing_by all_goals simp_wf; all_goals omega

/-- The transport covers the full reference premise syntax, including
quantifiers and object-binder scopes, without changing scope instantiation. -/
theorem reference_premise_same_core {first second : LanguageDef}
    (sameCore : first.rewrites.map ruleCore = second.rewrites.map ruleCore)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {initial final : Bindings}
    {premise : Premise} {witness : ReferenceStep.Witness}
    (held : ReferenceStep.PremiseValid relEnv first sites initial premise witness final) :
    ReferenceStep.PremiseValid relEnv second sites initial premise witness final :=
  match held with
  | .base shape member => by
      have languageUnused : Engine.premiseStepWithEnv relEnv first initial premise =
          Engine.premiseStepWithEnv relEnv second initial premise := by
        cases premise <;> rfl
      exact .base shape (languageUnused ▸ member)
  | .step endpoints child matched merged => .step endpoints
      (reference_step_same_core sameCore relEnv child) matched merged
  | .forAll selected bodies => .forAll selected (reference_elements_same_core sameCore relEnv bodies)
 termination_by sizeOf witness
 decreasing_by all_goals simp_wf; all_goals omega

/-- Quantified transport preserves every local source witness and its
carrier order. It does not identify their evidence occurrences. -/
theorem reference_elements_same_core {first second : LanguageDef}
    (sameCore : first.rewrites.map ruleCore = second.rewrites.map ruleCore)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise} {items : List Pattern} {witnesses : List ReferenceStep.Witness}
    (held : ReferenceStep.ForAllValid relEnv first sites bindings parameter body items witnesses) :
    ReferenceStep.ForAllValid relEnv second sites bindings parameter body items witnesses :=
  match held with
  | .nil => .nil
  | .cons head tail => .cons (reference_premise_same_core sameCore relEnv head)
      (reference_elements_same_core sameCore relEnv tail)
 termination_by sizeOf witnesses
 decreasing_by all_goals simp_wf; all_goals omega
end

/-- Indexed rule-core equality preserves and reflects the original full
reference relation, independently of annotation storage. -/
theorem reference_step_same_core_iff {first second : LanguageDef}
    (sameCore : first.rewrites.map ruleCore = second.rewrites.map ruleCore)
    (relEnv : Engine.RelationEnv) {source target : Pattern} :
    ReferenceStep.Step relEnv first source target ↔ ReferenceStep.Step relEnv second source target := by
  constructor
  · rintro ⟨witness,step⟩
    exact ⟨witness,reference_step_same_core sameCore relEnv step⟩
  · rintro ⟨witness,step⟩
    exact ⟨witness,reference_step_same_core sameCore.symm relEnv step⟩

#print axioms reference_step_same_core
#print axioms reference_premises_same_core
#print axioms reference_premise_same_core
#print axioms reference_elements_same_core
#print axioms reference_step_same_core_iff

/-- The ordinary interpreted source bridge also supplies the same witness to
an explicitly declared internal equation policy. This is preservation, not a
canonical-matcher completeness assertion. -/
theorem directed_root_toDeclaredReference_of_forward {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedForwardProfile Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    (unconditional : ReferenceStep.UnconditionalEquations environment.language)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index bindings witnesses) target
      (ReferenceStep.declaredBoundaryPolicy relEnv environment.language unconditional) := by
  obtain ⟨bindings,witnesses,step⟩ := directed_root_toReference_of_forward profile relEnv reads fired
  exact ⟨bindings,witnesses,ReferenceStep.stepValid_equational_of_presentation
    (ReferenceStep.equivalentSetoid relEnv environment.language) _ step⟩

#print axioms directed_root_toDeclaredReference_of_forward

theorem directed_root_toDeclaredReference {Schema : Pattern → Prop} [BinderFreeSyntax Schema] {environment : GeneralPremise.Environment}
    (profile : DirectedProfileWith Schema environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    (unconditional : ReferenceStep.UnconditionalEquations environment.language)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    ∃ bindings witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index bindings witnesses) target
      (ReferenceStep.declaredBoundaryPolicy relEnv environment.language unconditional) :=
  directed_root_toDeclaredReference_of_forward profile.forward relEnv reads unconditional fired

/-- On the genuine equation-free specialization, the full recursive typed
ordinary interpretation agrees with the explicit declared internal policy. -/
theorem directed_root_iff_declared_of_isEquationFree {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    (unconditional : ReferenceStep.UnconditionalEquations environment.language)
    (free : environment.language.isEquationFree = true)
    {source target : Pattern} {index : Nat} {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ trace captured completed history,GeneralPremise.RootFiring environment bound type source index
      trace captured completed history target) ↔
    ∃ initial witnesses,ReferenceStep.StepValid relEnv environment.language source
      (.rule index initial witnesses) target
      (ReferenceStep.declaredBoundaryPolicy relEnv environment.language unconditional) := by
  constructor
  · rintro ⟨trace,captured,completed,history,fired⟩
    exact directed_root_toDeclaredReference profile relEnv reads unconditional fired
  · rintro ⟨initial,witnesses,step⟩
    exact (directed_root_iff_reference profile relEnv reads sourceTyped).mpr
      ⟨initial,witnesses,(ReferenceStep.stepValid_declared_iff_of_isEquationFree unconditional free _).mp step⟩

theorem directed_step_iff_declared_of_isEquationFree {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    (unconditional : ReferenceStep.UnconditionalEquations environment.language)
    (free : environment.language.isEquationFree = true)
    {source target : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ index trace captured completed history,GeneralPremise.RootFiring environment bound type source index
      trace captured completed history target) ↔
    ReferenceStep.StepWith (ReferenceStep.declaredBoundaryPolicy relEnv environment.language unconditional)
      relEnv environment.language source target :=
  (directed_step_iff_reference profile relEnv reads sourceTyped).trans
    (ReferenceStep.stepWith_declared_iff_of_isEquationFree unconditional free).symm

theorem directed_step_iff_declaredModulo_of_isEquationFree {environment : GeneralPremise.Environment}
    (profile : DirectedProfile environment) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv environment.provider)
    (unconditional : ReferenceStep.UnconditionalEquations environment.language)
    (free : environment.language.isEquationFree = true)
    {source target : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (∃ index trace captured completed history,GeneralPremise.RootFiring environment bound type source index
      trace captured completed history target) ↔
    ReferenceStep.StepModuloWith relEnv environment.language
      (ReferenceStep.declaredBoundaryPolicy relEnv environment.language unconditional) source target :=
  (directed_step_iff_reference profile relEnv reads sourceTyped).trans
    (ReferenceStep.stepModuloWith_declared_iff_of_isEquationFree unconditional free).symm

#print axioms directed_root_toDeclaredReference
#print axioms directed_root_iff_declared_of_isEquationFree
#print axioms directed_step_iff_declared_of_isEquationFree
#print axioms directed_step_iff_declaredModulo_of_isEquationFree

#print axioms DirectedValidation.step_shape
end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.QuantifiedReference
