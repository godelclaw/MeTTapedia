import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaProjection
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCaptureRepresentations

/-!
# Static representation admission for total premise execution

Available names and representation refinements follow the authored order.
Finite collections originate in actual rest captures or checked provider
values. Atomic names originate in checked provider outputs. Quantifier
parameters are lexical, and an empty quantifier grants no new outer names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding ScopedRuleMatching

structure Refinement where
  available : List String
  finite : List String
  atomic : List String
  deriving DecidableEq, Repr

def Refinement.Holds (assignment : Assignment) (refinement : Refinement) : Prop :=
  BoundNames assignment refinement.available ∧
    FiniteCaptureNames assignment refinement.finite ∧
    AtomicCaptureNames assignment refinement.atomic

def initialRefinement (rule : RewriteRule) : Refinement :=
  ⟨rule.left.freeFvarNames, restCaptureNames rule.left, []⟩

def checkFiniteValue : Pattern → Bool
  | .collection _ _ none => true
  | _ => false

def checkAtomicValue : Pattern → Bool
  | .fvar _ => true
  | _ => false

def checkProviderRepresentation (provider : ProviderSnapshot) (relation : String)
    (index : Nat) (check : Pattern → Bool) : Bool :=
  provider.rows.all fun row => row.relation != relation ||
    match row.values[index]? with
    | some value => check value
    | none => false

def representedOutputNames (provider : ProviderSnapshot) (relation : String)
    (check : Pattern → Bool) : Nat → List Pattern → List RelationArgMode → List String
  | _, [], [] => []
  | index, schema :: schemas, mode :: modes =>
      let names := match mode, schema with
        | .output, .fvar name =>
            if checkProviderRepresentation provider relation index check then [name] else []
        | _, _ => []
      names ++ representedOutputNames provider relation check (index + 1) schemas modes
  | _, _, _ => []

def outputRestNames : List Pattern → List RelationArgMode → List String
  | [], [] => []
  | schema :: schemas, mode :: modes =>
      (match mode with | .input => [] | .output => restCaptureNames schema) ++
        outputRestNames schemas modes
  | _, _ => []

def checkQueryInputs (rule : RewriteRule) (spec : RuleBindingSpec)
    (premiseIndex quantifierDepth : Nat) (available : List String) :
    Nat → List Pattern → List RelationArgMode → Bool
  | _, [], [] => true
  | index, schema :: schemas, mode :: modes =>
      (match mode with
        | .input => checkRootProjectionSchema rule spec
            (.premise premiseIndex quantifierDepth index) [] schema &&
            namesAvailable available schema.freeFvarNames
        | .output => true) &&
      checkQueryInputs rule spec premiseIndex quantifierDepth available (index + 1) schemas modes
  | _, _, _ => false

structure CheckedFlow where
  refinement : Refinement
  supported : Bool
  deriving DecidableEq, Repr

def premiseFlow (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) (premiseIndex quantifierDepth : Nat)
    (refinement : Refinement) : Premise → CheckedFlow
  | .relationQuery relation arguments =>
      match signature? provider relation arguments.length with
      | none => ⟨refinement, false⟩
      | some signature =>
          ⟨⟨queryOutputNames arguments signature.modes ++ refinement.available,
              outputRestNames arguments signature.modes ++
                representedOutputNames provider relation checkFiniteValue 0 arguments signature.modes ++
                refinement.finite,
              representedOutputNames provider relation checkAtomicValue 0 arguments signature.modes ++
                refinement.atomic⟩,
            checkQueryInputs rule spec premiseIndex quantifierDepth refinement.available
              0 arguments signature.modes⟩
  | .freshness condition =>
      ⟨refinement, (refinement.atomic.contains condition.varName ||
          (lookupRuleType? rule condition.varName).isNone) &&
        checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth 0)
          [] condition.term && namesAvailable refinement.available condition.term.freeFvarNames⟩
  | .forAll collection parameter body =>
      let localRefinement : Refinement :=
        ⟨parameter :: refinement.available, refinement.finite.filter (· != parameter),
          refinement.atomic.filter (· != parameter)⟩
      let localFlow := premiseFlow language provider rule spec premiseIndex
        (quantifierDepth + 1) localRefinement body
      let types := match lookupRuleType? rule collection, lookupRuleType? rule parameter with
        | some (.collection _ element), some parameterType =>
            element == parameterType && dependencies? spec parameter == some []
        | _, _ => false
      ⟨refinement, refinement.finite.contains collection && types && localFlow.supported⟩
  | .congruence source target =>
      ⟨⟨target.freeFvarNames ++ refinement.available,
          restCaptureNames target ++ refinement.finite, refinement.atomic⟩,
        (match sourceType? language rule source with
          | some type => schemaValuesChecked language rule [] [source] [type]
          | none => false) &&
          source.hasCanonicalBinderMetadata &&
          checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth 0) [] source &&
          namesAvailable refinement.available source.freeFvarNames⟩
  | .scopedStep step =>
      ⟨⟨step.target.freeFvarNames ++ refinement.available,
          restCaptureNames step.target ++ refinement.finite, refinement.atomic⟩,
        schemaValuesChecked language rule step.binders [step.source] [step.resultType] &&
        step.source.hasCanonicalBinderMetadata &&
        checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth 0) [] step.source &&
          namesAvailable refinement.available step.source.freeFvarNames⟩

def premisesFlow (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) :
    Nat → Refinement → List Premise → CheckedFlow
  | _, refinement, [] => ⟨refinement, true⟩
  | index, refinement, premise :: premises =>
      let head := premiseFlow language provider rule spec index 0 refinement premise
      let tail := premisesFlow language provider rule spec (index + 1) head.refinement premises
      ⟨tail.refinement, head.supported && tail.supported⟩

def checkRule (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  let flow := premisesFlow language provider rule spec 0 (initialRefinement rule) rule.premises
  checkZeroDependencies spec && flow.supported &&
    checkRootProjectionSchema rule spec .right [] rule.right &&
    namesAvailable flow.refinement.available rule.right.freeFvarNames

def checkLanguage (environment : Environment) : Bool :=
  environment.language.rewrites.zipIdx.all fun (rule, index) =>
    match specification? environment index with
    | none => false
    | some spec => admittedFor rule spec && checkRule environment.language environment.provider rule spec

theorem checkLanguage_rule {environment : Environment}
    (checked : checkLanguage environment = true) {index : Nat} {rule : RewriteRule}
    (declared : environment.language.rewrites[index]? = some rule) :
    ∃ spec, specification? environment index = some spec ∧ admittedFor rule spec = true ∧
      checkRule environment.language environment.provider rule spec = true := by
  have member : (rule, index) ∈ environment.language.rewrites.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr declared
  have ruleChecked := List.all_eq_true.mp checked (rule, index) member
  cases specified : specification? environment index with
  | none => simp [specified] at ruleChecked
  | some spec =>
    exact ⟨spec, rfl, by simpa only [specified, Bool.and_eq_true] using ruleChecked⟩

theorem initialRefinement_holds {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {target : Pattern} {initial final : Assignment}
    (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      rule.left target final) : (initialRefinement rule).Holds final := by
  exact ⟨matching_bound_names matching, matching_finite_restCaptures matching,
    by intro name member; simp [initialRefinement] at member⟩

theorem checkProviderRepresentation_sound {provider : ProviderSnapshot} {relation : String}
    {index : Nat} {check : Pattern → Bool}
    (checked : checkProviderRepresentation provider relation index check = true)
    (row : ProviderRow) (member : row ∈ provider.rows) (same : row.relation = relation) :
    ∃ value, row.values[index]? = some value ∧ check value = true := by
  have rowChecked := List.all_eq_true.mp checked row member
  simp only [same, bne_self_eq_false, Bool.false_or] at rowChecked
  split at rowChecked
  · rename_i value found
    exact ⟨value, found, rowChecked⟩
  · contradiction

theorem checkFiniteValue_sound {value : Pattern} (checked : checkFiniteValue value = true) :
    ∃ kind elements, value = .collection kind elements none := by
  cases value <;> simp_all [checkFiniteValue]
  split at checked <;> simp_all

theorem checkAtomicValue_sound {value : Pattern} (checked : checkAtomicValue value = true) :
    ∃ atom, value = .fvar atom := by
  cases value <;> simp_all [checkAtomicValue]

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
