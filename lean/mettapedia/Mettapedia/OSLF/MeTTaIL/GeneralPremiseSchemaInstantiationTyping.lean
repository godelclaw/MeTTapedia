import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaProjection
import Mettapedia.GSLT.LanguageDef.TypedOccurrenceSubstitution
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding

/-!
# Sorted structural premise instantiation

Dependency-free captured values are reindexed into the exact local binder
prefix. The actual occurrence traversal preserves constructor argument
representations and typing, including explicit scoped substitution. Object
free names and authored schema metavariables keep their separate contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem findType_eq_lookup (entries : List (String × TypeExpr)) (name : String) :
    (entries.find? fun entry => entry.1 == name).map Prod.snd = entries.lookup name := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, type⟩
      by_cases same : key = name
      · subst key
        simp [List.find?, List.lookup]
      · have forward : (key == name) = false := beq_eq_false_iff_ne.mpr same
        have backward : (name == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        simp only [List.find?, List.lookup, forward, backward, ih]

theorem lookupRuleType?_eq_lookup (rule : RewriteRule) (name : String) :
    lookupRuleType? rule name = rule.typeContext.lookup name :=
  findType_eq_lookup rule.typeContext name

theorem instantiateAt?_preservesRepresentation
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment : Assignment}
    {schema actual : Pattern} {parameter : TermParam}
    (representation : MatchesParameterRepresentation parameter schema)
    (projected : instantiateAt? rule spec ambient site path depth assignment schema = some actual) :
    MatchesParameterRepresentation parameter actual := by
  cases parameter with
  | simple => exact True.intro
  | abstractionNamed binder body type =>
      obtain ⟨schemaBody, same⟩ := (matchesParameterRepresentation_abstractionNamed_iff
        binder body type schema).mp representation
      subst schema
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at projected
      obtain ⟨actualBody, _, same⟩ := projected
      subst actual
      exact True.intro
  | multiAbstractionNamed binders body type =>
      obtain ⟨arity, schemaBody, same⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff
        binders body type schema).mp representation
      subst schema
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at projected
      obtain ⟨actualBody, _, same⟩ := projected
      subst actual
      exact True.intro

theorem projected_capture_typed
    {environment : Environment} {context : Context} {assignment : Assignment}
    {name : String} {expected : TypeExpr} {locals : List TypeExpr} {actual : Pattern}
    (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true)
    (declared : lookupRuleType? context.rule name = some expected)
    (projected : ∃ value, lookup assignment name = some value ∧
      instantiateValue? value context.bound.length locals.length [] = some actual) :
    HasType environment.language environment.free (locals ++ context.bound) actual expected := by
  obtain ⟨value, found, projected⟩ := projected
  obtain ⟨dependencies, storedType, dependencyFound, typeFound, storedDependencies, ambient, bodyTyped⟩ :=
    typed.1 name value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  have noDependencies := checkZeroDependencies_sound context.spec zero name dependencies dependencyFound
  have sameType : storedType = expected :=
    Option.some.inj (typeFound.symm.trans ((lookupRuleType?_eq_lookup context.rule name) ▸ declared))
  subst storedType
  have body : HasType environment.language environment.free context.bound value.body expected := by
    simpa only [noDependencies, List.nil_append] using bodyTyped
  have asRecord : value = { dependencies := [], ambient := context.bound.length, body := value.body } := by
    cases value
    simp_all only
  rw [asRecord] at projected
  have returned := instantiateValue?_typedList (locals := locals) (dependencies := []) body
    (List.Forall₂.nil : List.Forall₂
      (fun argument dependency => HasType environment.language environment.free
        (locals ++ context.bound) argument dependency) [] [])
  have same := Option.some.inj (returned.symm.trans projected)
  rw [← same]
  exact body.substituteOccurrenceList List.Forall₂.nil

mutual
  theorem instantiateAt?_typed
      {environment : Environment} {context : Context} {assignment : Assignment}
      {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
      {schema actual : Pattern} {expected : TypeExpr}
      (typed : TypedAssignment environment context assignment)
      (zero : checkZeroDependencies context.spec = true)
      (checked : checkRootProjectionSchema context.rule context.spec site path schema = true)
      (schemaTyped : HasType environment.language (lookupRuleType? context.rule) locals schema expected)
      (projected : instantiateAt? context.rule context.spec context.bound.length site path
        locals.length assignment schema = some actual) :
      HasType environment.language environment.free (locals ++ context.bound) actual expected := by
    cases schemaTyped with
    | bvar found =>
        simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at projected
        subst actual
        exact .bvar (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found)
    | fvar found =>
        have arguments : arguments? context.rule context.spec _ site path = some [] :=
          beq_iff_eq.mp checked
        simp only [instantiateAt?, instantiateWith?, arguments, Option.bind_eq_bind,
          Option.bind_some, Option.bind_eq_some_iff] at projected
        exact projected_capture_typed typed zero found projected
    | constructor member ordinary argumentsTyped =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualArguments, read, same⟩ := projected
        subst actual
        exact .constructor member ordinary (instantiateArgsAt?_typed typed zero checked argumentsTyped read)
    | @lambda _ binder schemaBody domain codomain bodyTyped =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) schemaBody = true := checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        apply HasType.lambda
        exact instantiateAt?_typed (locals := domain :: locals) typed zero bodyChecked bodyTyped read
    | @multiLambda _ arity binders schemaBody domain codomain bodyTyped =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) schemaBody = true := checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        apply HasType.multiLambda
        have bodyRead : instantiateAt? context.rule context.spec context.bound.length site (path ++ [0])
            (List.replicate arity domain ++ locals).length assignment schemaBody = some actualBody := by
          simpa only [instantiateAt?, List.length_append, List.length_replicate, Nat.add_comm] using read
        simpa only [List.append_assoc] using
          instantiateAt?_typed (locals := List.replicate arity domain ++ locals) typed zero bodyChecked bodyTyped bodyRead
    | subst bodyTyped replacementTyped =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true] at checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, bodyRead, actualReplacement, replacementRead, same⟩ := projected
        subst actual
        have body := instantiateAt?_typed (locals := _ :: locals) typed zero checked.1 bodyTyped bodyRead
        have replacement := instantiateAt?_typed typed zero checked.2 replacementTyped replacementRead
        exact body.instantiateBVar replacement
    | collection elementsTyped =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true, Option.isNone_iff_eq_none] at checked
        rcases checked with ⟨restNone, checked⟩
        subst restNone
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualElements, read, same⟩ := projected
        subst actual
        exact .collection (instantiateElementsAt?_typed typed zero checked elementsTyped read)
    | collectionConstructor member shape elementsTyped =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true, Option.isNone_iff_eq_none] at checked
        rcases checked with ⟨restNone, checked⟩
        subst restNone
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualElements, read, same⟩ := projected
        subst actual
        exact .collectionConstructor member shape
          (instantiateElementsAt?_typed typed zero checked elementsTyped read)
  termination_by sizeOf schema
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem instantiateArgsAt?_typed
      {environment : Environment} {context : Context} {assignment : Assignment}
      {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat} {index : Nat}
      {schemas actuals : List Pattern} {parameters : List TermParam}
      (typed : TypedAssignment environment context assignment)
      (zero : checkZeroDependencies context.spec = true)
      (checked : checkRootProjectionArguments context.rule context.spec site path index schemas = true)
      (schemaTyped : ArgumentsHaveTypes environment.language (lookupRuleType? context.rule) locals schemas parameters)
      (projected : instantiateArgsWith? instantiateBVar context.rule context.spec context.bound.length
        site path locals.length assignment index schemas = some actuals) :
      ArgumentsHaveTypes environment.language environment.free (locals ++ context.bound) actuals parameters := by
    cases schemaTyped with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at projected
        subst actuals
        exact .nil
    | cons representation expected headTyped tailTyped =>
        simp only [checkRootProjectionArguments, Bool.and_eq_true] at checked
        simp only [instantiateArgsWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨head, headRead, tail, tailRead, same⟩ := projected
        subst actuals
        exact .cons (instantiateAt?_preservesRepresentation representation headRead) expected
          (instantiateAt?_typed typed zero checked.1 headTyped headRead)
          (instantiateArgsAt?_typed typed zero checked.2 tailTyped tailRead)
  termination_by sizeOf schemas
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem instantiateElementsAt?_typed
      {environment : Environment} {context : Context} {assignment : Assignment}
      {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat} {index : Nat}
      {schemas actuals : List Pattern} {elementType : TypeExpr}
      (typed : TypedAssignment environment context assignment)
      (zero : checkZeroDependencies context.spec = true)
      (checked : checkRootProjectionArguments context.rule context.spec site path index schemas = true)
      (schemaTyped : ElementsHaveType environment.language (lookupRuleType? context.rule) locals schemas elementType)
      (projected : instantiateArgsWith? instantiateBVar context.rule context.spec context.bound.length
        site path locals.length assignment index schemas = some actuals) :
      ElementsHaveType environment.language environment.free (locals ++ context.bound) actuals elementType := by
    cases schemaTyped with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at projected
        subst actuals
        exact .nil _ _
    | cons headTyped tailTyped =>
        simp only [checkRootProjectionArguments, Bool.and_eq_true] at checked
        simp only [instantiateArgsWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨head, headRead, tail, tailRead, same⟩ := projected
        subst actuals
        exact .cons (instantiateAt?_typed typed zero checked.1 headTyped headRead)
          (instantiateElementsAt?_typed typed zero checked.2 tailTyped tailRead)
  termination_by sizeOf schemas
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

#print axioms instantiateAt?_typed
#print axioms instantiateArgsAt?_typed

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
