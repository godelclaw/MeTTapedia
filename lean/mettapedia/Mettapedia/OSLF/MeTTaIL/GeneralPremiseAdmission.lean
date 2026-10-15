import Mettapedia.OSLF.MeTTaIL.GeneralPremiseWeakening
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping

/-!
# Executable premise flow and declaration-derived child strata

Relations carry explicit modes. Quantified parameters are local, and an empty
quantification cannot produce a newly available outer binding. Directed step
calls use the actual authored declaration order; no external rank or oracle
is supplied. A known constructor head narrows child candidates. An unknown
head remains conservative and normally exposes a cycle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def namesAvailable (available required : List String) : Bool :=
  required.all fun name => available.contains name

theorem namesAvailable_sound (available required : List String)
    (checked : namesAvailable available required = true) :
    ∀ name ∈ required, name ∈ available := by
  intro name member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp checked name member)

def lookupRuleType? (rule : RewriteRule) (name : String) : Option TypeExpr :=
  (rule.typeContext.find? fun entry => entry.1 == name).map Prod.snd

def collectionElement? (language : LanguageDef) (type : TypeExpr) :
    Option (CollType × TypeExpr) :=
  match type with
  | .collection kind element => some (kind, element)
  | .base category =>
      let alternatives := language.terms.filterMap fun declaration =>
        if declaration.category == category then
          match declaration.params with
          | [.simple _ (.collection kind element)] => some (kind, element)
          | _ => none
        else none
      match alternatives.eraseDups with
      | [candidate] => some candidate
      | _ => none
  | _ => none

def sourceType? (language : LanguageDef) (rule : RewriteRule) : Pattern → Option TypeExpr
  | .fvar name => lookupRuleType? rule name
  | .apply constructor _ =>
      match language.terms.filter fun declaration => declaration.label == constructor with
      | [declaration] => some (.base declaration.category)
      | _ => none
  | _ => none

def schemaValuesChecked (language : LanguageDef) (rule : RewriteRule)
    (bound : List TypeExpr) : List Pattern → List TypeExpr → Bool
  | [], [] => true
  | pattern :: patterns, type :: types =>
      SchemaTyping.checkSchemaType (SchemaTyping.declaredDomains language rule bound)
        language ((fun name => lookupRuleType? rule name)) bound pattern type &&
        schemaValuesChecked language rule bound patterns types
  | _, _ => false

theorem schemaValuesChecked_sound {language : LanguageDef} {rule : RewriteRule}
    {bound : List TypeExpr} {patterns : List Pattern} {types : List TypeExpr}
    (checked : schemaValuesChecked language rule bound patterns types = true) :
    List.Forall₂ (HasType language (fun name => lookupRuleType? rule name) bound) patterns types := by
  induction patterns generalizing types with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons type types => simp [schemaValuesChecked] at checked
  | cons pattern patterns ih =>
      cases types with
      | nil => simp [schemaValuesChecked] at checked
      | cons type types =>
          simp only [schemaValuesChecked, Bool.and_eq_true] at checked
          exact .cons (SchemaTyping.checkSchemaType_sound checked.1) (ih checked.2)

theorem schemaValuesChecked_complete_objects {language : LanguageDef} {rule : RewriteRule}
    {bound : List TypeExpr} {patterns : List Pattern} {types : List TypeExpr}
    (typed : List.Forall₂
      (HasType language (fun name => lookupRuleType? rule name) bound) patterns types)
    (objects : isObjectPatternList patterns = true) :
    schemaValuesChecked language rule bound patterns types = true := by
  induction typed with
  | nil => rfl
  | cons head tail ih =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      simp only [schemaValuesChecked, Bool.and_eq_true]
      exact ⟨SchemaTyping.checkSchemaType_complete_of_object head objects.1, ih objects.2⟩

structure FlowResult where
  available : List String
  supported : Bool
  deriving DecidableEq, Repr

def queryInputNames (arguments : List Pattern) (modes : List RelationArgMode) : List String :=
  (arguments.zip modes).flatMap fun (argument, mode) =>
    match mode with
    | .input => argument.freeFvarNames
    | .output => []

def queryOutputNames (arguments : List Pattern) (modes : List RelationArgMode) : List String :=
  (arguments.zip modes).flatMap fun (argument, mode) =>
    match mode with
    | .input => []
    | .output => argument.freeFvarNames

def premiseFlow (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (available : List String) : Premise → FlowResult
  | .relationQuery relation arguments =>
      match signature? provider relation arguments.length with
      | none => ⟨available, false⟩
      | some signature =>
          ⟨(queryOutputNames arguments signature.modes ++ available).eraseDups,
            namesAvailable available (queryInputNames arguments signature.modes) &&
              schemaValuesChecked language rule [] arguments signature.argumentTypes⟩
  | .freshness condition =>
      let typed := match sourceType? language rule condition.term with
        | none => false
        | some type => SchemaTyping.checkSchemaType
            (SchemaTyping.declaredDomains language rule [])
            language ((fun name => lookupRuleType? rule name)) [] condition.term type
      ⟨available, (available.contains condition.varName ||
          (lookupRuleType? rule condition.varName).isNone) &&
        namesAvailable available condition.term.freeFvarNames && typed⟩
  | .congruence source target =>
      let typed := match sourceType? language rule source with
        | none => false
        | some type => schemaValuesChecked language rule [] [source, target] [type, type]
      ⟨(target.freeFvarNames ++ available).eraseDups,
        namesAvailable available source.freeFvarNames && typed⟩
  | .scopedStep step =>
      ⟨(step.target.freeFvarNames ++ available).eraseDups,
        namesAvailable available step.source.freeFvarNames &&
          schemaValuesChecked language rule step.binders
            [step.source, step.target] [step.resultType, step.resultType]⟩
  | .forAll collection parameter body =>
      let localFlow := premiseFlow language provider rule spec (parameter :: available) body
      let typed := do
        let collectionType ← lookupRuleType? rule collection
        let (_, elementType) ← collectionElement? language collectionType
        let parameterType ← lookupRuleType? rule parameter
        if parameterType == elementType && dependencies? spec parameter == some []
          then some () else none
      ⟨available, available.contains collection && typed.isSome && localFlow.supported⟩

def premisesFlow (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) : List String → List Premise → FlowResult
  | available, [] => ⟨available, true⟩
  | available, premise :: premises =>
      let next := premiseFlow language provider rule spec available premise
      let tail := premisesFlow language provider rule spec next.available premises
      ⟨tail.available, next.supported && tail.supported⟩

@[simp] theorem forall_flow_preserves_available (language : LanguageDef)
    (provider : ProviderSnapshot) (rule : RewriteRule) (spec : RuleBindingSpec)
    (available : List String) (collection parameter : String) (body : Premise) :
    (premiseFlow language provider rule spec available
      (.forAll collection parameter body)).available = available := rfl

def rulePremisesAdmitted (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  let flow := premisesFlow language provider rule spec rule.left.freeFvarNames rule.premises
  flow.supported && namesAvailable flow.available rule.right.freeFvarNames

/-- An instantiated constructor source retains its head. Unknown source heads
conservatively permit every candidate, including the current declaration. -/
def potentialChild (source : Pattern) (candidate : RewriteRule) : Bool :=
  match source with
  | .apply expected _ =>
      match candidate.left with
      | .apply actual _ => actual == expected
      | .fvar _ => true
      | _ => false
  | _ => true

def stepSources : Premise → List Pattern
  | .congruence source _ => [source]
  | .scopedStep step => [step.source]
  | .forAll _ _ body => stepSources body
  | _ => []

def checkStepStratification (language : LanguageDef) : Bool :=
  language.rewrites.zipIdx.all fun (rule, parentIndex) =>
    (rule.premises.flatMap stepSources).all fun source =>
      language.rewrites.zipIdx.all fun (candidate, childIndex) =>
        !(potentialChild source candidate) || decide (childIndex < parentIndex)

theorem checkStepStratification_child (language : LanguageDef)
    (checked : checkStepStratification language = true)
    (rule candidate : RewriteRule) (parentIndex childIndex : Nat)
    (parent : (rule, parentIndex) ∈ language.rewrites.zipIdx)
    (child : (candidate, childIndex) ∈ language.rewrites.zipIdx)
    (source : Pattern) (called : source ∈ rule.premises.flatMap stepSources)
    (possible : potentialChild source candidate = true) : childIndex < parentIndex := by
  have ruleChecked := List.all_eq_true.mp checked (rule, parentIndex) parent
  have sourceChecked := List.all_eq_true.mp ruleChecked source called
  have childChecked := List.all_eq_true.mp sourceChecked (candidate, childIndex) child
  simpa only [possible, Bool.not_true, Bool.false_or, decide_eq_true_eq] using childChecked

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
