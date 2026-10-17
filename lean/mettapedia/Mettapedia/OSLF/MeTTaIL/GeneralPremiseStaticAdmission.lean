import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaProjection
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCaptureRepresentations
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationTyping

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
  !provider.dynamicRelations.contains relation &&
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

theorem checkProviderRepresentation_dynamic {provider : ProviderSnapshot} {relation : String}
    (registered : relation ∈ provider.dynamicRelations) (index : Nat) (check : Pattern → Bool) :
    checkProviderRepresentation provider relation index check = false := by
  simp only [checkProviderRepresentation, List.contains_iff_mem.mpr registered,
    Bool.not_true, Bool.false_and]

theorem checkProviderRepresentation_sound {provider : ProviderSnapshot} {relation : String}
    {index : Nat} {check : Pattern → Bool}
    (checked : checkProviderRepresentation provider relation index check = true)
    (row : ProviderRow) (member : row ∈ provider.rows) (same : row.relation = relation) :
    ∃ value, row.values[index]? = some value ∧ check value = true := by
  unfold checkProviderRepresentation at checked
  simp only [Bool.and_eq_true] at checked
  have rowChecked := List.all_eq_true.mp checked.2 row member
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

open GeneralFirstOrderProjection

mutual
  /-- First-order authored occurrences with declared empty dependencies pass
  the same root-projection checker used by static execution admission. -/
  theorem firstOrder_projection {rule : RewriteRule} {site : RulePatternSite}
      {path : List Nat} {schema : Pattern} (shape : FirstOrder schema)
      (coherent : NameCoherent rule site path schema)
      (declared : ∀ name ∈ schema.freeFvarNames,
        dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
      checkRootProjectionSchema rule (GeneralRuleBindingInference.inferredSpec rule) site path schema = true := by
    cases shape with
    | metavariable name =>
      exact beq_iff_eq.mpr (arguments?_empty_of_declared rule _ name site path
        (declared name (by simp [Pattern.freeFvarNames])) coherent.fvar rfl)
    | constructor label arguments shapes =>
      simpa only [checkRootProjectionSchema] using firstOrder_projection_arguments shapes coherent.arguments
        (by simpa only [Pattern.freeFvarNames] using declared)
  termination_by sizeOf schema

  theorem firstOrder_projection_arguments {rule : RewriteRule} {site : RulePatternSite}
      {path : List Nat} {index : Nat} {schemas : List Pattern}
      (shapes : ∀ schema ∈ schemas, FirstOrder schema)
      (coherent : ArgumentsNameCoherent rule site path index schemas)
      (declared : ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
        dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
      checkRootProjectionArguments rule (GeneralRuleBindingInference.inferredSpec rule) site path index schemas = true := by
    cases schemas with
    | nil => rfl
    | cons schema schemas =>
      simp only [checkRootProjectionArguments, Bool.and_eq_true]
      refine ⟨firstOrder_projection (shapes schema (List.mem_cons_self ..)) coherent.head ?_,
        firstOrder_projection_arguments (fun child member => shapes child (List.mem_cons_of_mem _ member))
          coherent.tail ?_⟩
      · intro name member
        exact declared name (List.mem_flatMap.mpr ⟨schema, List.mem_cons_self .., member⟩)
      · intro name member
        obtain ⟨child, childMember, present⟩ := List.mem_flatMap.mp member
        exact declared name (List.mem_flatMap.mpr ⟨child, List.mem_cons_of_mem _ childMember, present⟩)
  termination_by sizeOf schemas
end

theorem firstOrder_projection_of_typed {language : LanguageDef} {rule : RewriteRule}
    {site : RulePatternSite} {path : List Nat} {schema : Pattern} {type : TypeExpr}
    (unique : (rule.typeContext.map Prod.fst).Nodup) (shape : FirstOrder schema)
    (coherent : NameCoherent rule site path schema)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      (fun name => lookupRuleType? rule name) [] schema type) :
    checkRootProjectionSchema rule (GeneralRuleBindingInference.inferredSpec rule) site path schema = true := by
  apply firstOrder_projection shape coherent
  intro name member
  obtain ⟨type, found⟩ := typed.freeType_of_mem_freeFvarNames_of_isObjectPattern shape.isObject member
  rw [lookupRuleType?_eq_lookup] at found
  exact inferred_dependencies_of_lookup rule unique found

theorem namesAvailable_mono {before after required : List String} (included : before ⊆ after)
    (checked : namesAvailable before required = true) : namesAvailable after required = true := by
  apply List.all_eq_true.mpr
  intro name member
  exact List.contains_iff_mem.mpr (included (namesAvailable_sound _ _ checked name member))

theorem checkQueryInputs_of_projection {rule : RewriteRule} {spec : RuleBindingSpec}
    {premiseIndex quantifierDepth : Nat} {available : List String} :
    ∀ {schemas : List Pattern} {modes : List RelationArgMode} (index : Nat),
      schemas.length = modes.length →
      (∀ offset schema, schemas[offset]? = some schema →
        checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth (index + offset)) [] schema = true) →
      namesAvailable available (queryInputNames schemas modes) = true →
      checkQueryInputs rule spec premiseIndex quantifierDepth available index schemas modes = true
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, lengths, _, _ => by simp at lengths
  | _ :: _, [], _, lengths, _, _ => by simp at lengths
  | schema :: schemas, mode :: modes, index, lengths, projected, checked => by
    have tailProjection : ∀ offset child, schemas[offset]? = some child →
        checkRootProjectionSchema rule spec (.premise premiseIndex quantifierDepth (index + 1 + offset)) [] child = true := by
      intro offset child selected
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
        projected (offset + 1) child (by simpa using selected)
    have headProjection := projected 0 schema rfl
    simp only [Nat.add_zero] at headProjection
    have tailLengths : schemas.length = modes.length := by simpa using lengths
    cases mode with
    | input =>
      have splitNames : namesAvailable available schema.freeFvarNames = true ∧
          namesAvailable available (queryInputNames schemas modes) = true := by
        simpa only [queryInputNames, List.zip_cons_cons, List.flatMap_cons, namesAvailable,
          List.all_append, Bool.and_eq_true] using checked
      simp only [checkQueryInputs, headProjection, splitNames.1, Bool.true_and]
      exact checkQueryInputs_of_projection (index + 1) tailLengths tailProjection splitNames.2
    | output =>
      have tailChecked : namesAvailable available (queryInputNames schemas modes) = true := by
        simpa only [queryInputNames, List.zip_cons_cons, List.flatMap_cons, List.nil_append] using checked
      simp only [checkQueryInputs, Bool.true_and]
      exact checkQueryInputs_of_projection (index + 1) tailLengths tailProjection tailChecked

/-- The existing ordered admission fold supplies the supported local flow
at every selected premise, with the available names earned by its prefix. -/
theorem premiseFlow_supported_at (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) :
    ∀ (pending : List Premise) (available : List String) (offset : Nat) (premise : Premise),
      (GeneralPremise.premisesFlow language provider rule spec available pending).supported = true →
      pending[offset]? = some premise →
      ∃ before, (GeneralPremise.premiseFlow language provider rule spec before premise).supported = true
  | [], _, _, _, _, selected => by cases selected
  | head :: pending, available, 0, premise, supported, selected => by
    cases Option.some.inj selected
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
    exact ⟨available, supported.1⟩
  | head :: pending, available, offset + 1, premise, supported, selected => by
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
    exact premiseFlow_supported_at language provider rule spec pending
      (GeneralPremise.premiseFlow language provider rule spec available head).available offset premise
      supported.2 selected

/-- Transport the existing admission flow through the richer static
refinement. Static availability keeps list layout; only membership is used. -/
theorem queryFlow_of_projection (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) :
    ∀ (pending : List Premise) (position : Nat) (available : List String) (refinement : Refinement),
      available ⊆ refinement.available →
      (∀ premise ∈ pending, ∃ relation arguments, premise = .relationQuery relation arguments) →
      (∀ offset relation arguments, pending[offset]? = some (.relationQuery relation arguments) →
        ∀ argumentIndex schema, arguments[argumentIndex]? = some schema →
          checkRootProjectionSchema rule spec (.premise (position + offset) 0 argumentIndex) [] schema = true) →
      (GeneralPremise.premisesFlow language provider rule spec available pending).supported = true →
      (premisesFlow language provider rule spec position refinement pending).supported = true ∧
      (GeneralPremise.premisesFlow language provider rule spec available pending).available ⊆
        (premisesFlow language provider rule spec position refinement pending).refinement.available
  | [], _, _, _, included, _, _, _ => ⟨rfl, included⟩
  | premise :: pending, position, available, refinement, included, queries, projected, supported => by
    obtain ⟨relation, arguments, rfl⟩ := queries premise (List.mem_cons_self ..)
    simp only [GeneralPremise.premisesFlow, Bool.and_eq_true] at supported
    cases found : signature? provider relation arguments.length with
    | none => simp [GeneralPremise.premiseFlow, found] at supported
    | some signature =>
      have headChecked := supported.1
      simp only [GeneralPremise.premiseFlow, found, Bool.and_eq_true] at headChecked
      have lengths := (signature?_readout _ _ _ _ found).2.2.2
      have headProjected : ∀ argumentIndex schema, arguments[argumentIndex]? = some schema →
          checkRootProjectionSchema rule spec (.premise position 0 argumentIndex) [] schema = true := by
        intro argumentIndex schema selected
        simpa using projected 0 relation arguments rfl argumentIndex schema selected
      have staticInputs := checkQueryInputs_of_projection 0 lengths.symm
        (fun offset schema selected => by simpa using headProjected offset schema selected)
        (namesAvailable_mono included headChecked.1)
      have nextIncluded :
          (GeneralPremise.premiseFlow language provider rule spec available (.relationQuery relation arguments)).available ⊆
          (premiseFlow language provider rule spec position 0 refinement (.relationQuery relation arguments)).refinement.available := by
        simp only [GeneralPremise.premiseFlow, premiseFlow, found]
        intro name member
        rcases List.mem_append.mp (List.mem_eraseDups.mp member) with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (included member)
      have tailProjected : ∀ offset rel args, pending[offset]? = some (.relationQuery rel args) →
          ∀ argumentIndex schema, args[argumentIndex]? = some schema →
            checkRootProjectionSchema rule spec (.premise (position + 1 + offset) 0 argumentIndex) [] schema = true := by
        intro offset rel args selected argumentIndex schema argument
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
          projected (offset + 1) rel args (by simpa using selected) argumentIndex schema argument
      have tail := queryFlow_of_projection language provider rule spec pending (position + 1) _ _ nextIncluded
        (fun item member => queries item (List.mem_cons_of_mem _ member)) tailProjected supported.2
      refine ⟨?_, tail.2⟩
      simpa only [premisesFlow, premiseFlow, found, staticInputs, Bool.true_and] using tail.1

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
