import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Executable schema typing with explicit substitutions

Object admission and schema admission remain distinct. Schema substitution
checks its body in the declared domain extension and its replacement in the
caller context. Domains are obtained from the finite authored type
vocabulary, including all nested declaration and metavariable types.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SchemaTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A schema tail is a declared collection-valued metavariable. Object
patterns still require a closed tail at their separate admission boundary. -/
def checkSchemaRest (free : FreeTypeContext) (kind : CollType) (element : TypeExpr) : Option String → Bool
  | none => true
  | some name => free name == some (.collection kind element)

mutual
  /-- Check one raw pattern against an expected type in the exact authored
  free and bound contexts. -/
  def checkSchemaType (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Bool :=
    match pattern with
    | .bvar index => bound[index]? == some expected
    | .fvar name => free name == some expected
    | .apply constructor arguments =>
        language.terms.any fun rule =>
          rule.label == constructor &&
            expected == .base rule.category &&
            !usesBareCollection? rule &&
            checkSchemaArguments domains language free bound arguments rule.params
    | .lambda _ body =>
        match expected with
        | .arrow domain codomain =>
            checkSchemaType domains language free (domain :: bound) body codomain
        | _ => false
    | .multiLambda arity _ body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            checkSchemaType domains language free
              (List.replicate arity domain ++ bound) body codomain
        | _ => false
    | .subst body replacement =>
        domains.any fun domain =>
          checkSchemaType domains language free (domain :: bound) body expected &&
            checkSchemaType domains language free bound replacement domain
    | .collection collectionType elements rest =>
        let direct :=
          match expected with
          | .collection actual elementType =>
              actual == collectionType &&
                checkSchemaElements domains language free bound elements elementType &&
                checkSchemaRest free collectionType elementType rest
          | _ => false
        let authored := language.terms.any fun rule =>
          match bareCollectionElementType? rule collectionType expected with
          | some elementType =>
              checkSchemaElements domains language free bound elements elementType &&
                checkSchemaRest free collectionType elementType rest
          | none => false
        direct || authored

  /-- Ordered argument-spine checker compiled from the authored parameter
  list. -/
  def checkSchemaArguments (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → List TermParam → Bool
    | [], [] => true
    | argument :: arguments, parameter :: parameters =>
        match parameterType? parameter with
        | some expected =>
            matchesParameterRepresentation? parameter argument &&
              checkSchemaType domains language free bound argument expected &&
              checkSchemaArguments domains language free bound arguments parameters
        | none => false
    | _, _ => false

  /-- Pointwise checker for collection elements. -/
  def checkSchemaElements (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → TypeExpr → Bool
    | [], _ => true
    | element :: elements, elementType =>
        checkSchemaType domains language free bound element elementType &&
          checkSchemaElements domains language free bound elements elementType
end

/-- Soundness of the argument-spine checker, assuming soundness for every
immediate argument pattern. -/
theorem checkSchemaArguments_sound_of
    {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (argumentSound : ∀ argument ∈ arguments, ∀ expected,
      checkSchemaType domains language free bound argument expected = true →
        HasType language free bound argument expected)
    (checked : checkSchemaArguments domains language free bound
      arguments parameters = true) :
    ArgumentsHaveTypes language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters =>
          simp [checkSchemaArguments] at checked
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => simp [checkSchemaArguments] at checked
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none =>
              simp [checkSchemaArguments, parameterTypeEquation] at checked
          | some expected =>
              simp only [checkSchemaArguments, parameterTypeEquation,
                Bool.and_eq_true] at checked
              rcases checked with
                ⟨⟨representationChecked, argumentChecked⟩, argumentsChecked⟩
              exact .cons
                ((matchesParameterRepresentation?_eq_true_iff
                  parameter argument).mp representationChecked)
                parameterTypeEquation
                (argumentSound argument (by simp) expected argumentChecked)
                (inductionHypothesis
                  (fun other membership otherExpected otherChecked =>
                    argumentSound other (by simp [membership])
                      otherExpected otherChecked)
                  argumentsChecked)

/-- Soundness of the collection-element checker, assuming soundness for every
immediate element pattern. -/
theorem checkSchemaElements_sound_of
    {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (elementSound : ∀ element ∈ elements,
      checkSchemaType domains language free bound element elementType = true →
        HasType language free bound element elementType)
    (checked : checkSchemaElements domains language free bound
      elements elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  induction elements with
  | nil => exact .nil bound elementType
  | cons element elements inductionHypothesis =>
      simp only [checkSchemaElements, Bool.and_eq_true] at checked
      exact .cons
        (elementSound element (by simp) checked.1)
        (inductionHypothesis
          (fun other membership otherChecked =>
            elementSound other (by simp [membership]) otherChecked)
          checked.2)

/-- Every successful executable check is a derivation in the sole declarative
typing relation authored by `LanguageDef`. -/
theorem checkSchemaType_sound
    {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (checked : checkSchemaType domains language free bound pattern expected = true) :
    HasType language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [checkSchemaType, beq_iff_eq] at checked
      exact .bvar checked
  | hfvar name =>
      simp only [checkSchemaType, beq_iff_eq] at checked
      exact .fvar checked
  | happly constructor arguments inductionHypothesis =>
      simp only [checkSchemaType, List.any_eq_true, Bool.and_eq_true,
        beq_iff_eq, Bool.not_eq_true'] at checked
      obtain ⟨rule, ruleMember,
        ⟨⟨⟨labelEquality, expectedEquality⟩, notBare⟩,
          argumentsChecked⟩⟩ := checked
      subst constructor
      subst expected
      exact .constructor ruleMember
        (by
          intro bare
          have bareChecked :=
            (usesBareCollection?_eq_true_iff rule).mpr bare
          rw [bareChecked] at notBare
          contradiction)
        (checkSchemaArguments_sound_of
          (fun argument membership argumentExpected argumentChecked =>
            inductionHypothesis argument membership argumentChecked)
          argumentsChecked)
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          exact .lambda (inductionHypothesis checked)
      | base sort => simp [checkSchemaType] at checked
      | multiBinder type => simp [checkSchemaType] at checked
      | collection collectionType elementType =>
          simp [checkSchemaType] at checked
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              exact .multiLambda (inductionHypothesis checked)
          | base sort => simp [checkSchemaType] at checked
          | arrow first second => simp [checkSchemaType] at checked
          | collection collectionType elementType =>
              simp [checkSchemaType] at checked
      | base sort => simp [checkSchemaType] at checked
      | multiBinder type => simp [checkSchemaType] at checked
      | collection collectionType elementType =>
          simp [checkSchemaType] at checked
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [checkSchemaType, List.any_eq_true, Bool.and_eq_true] at checked
      obtain ⟨domain, _, bodyChecked, replacementChecked⟩ := checked
      exact .subst (bodyHypothesis bodyChecked) (replacementHypothesis replacementChecked)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [checkSchemaType, Bool.or_eq_true, List.any_eq_true] at checked
      cases checked with
      | inl direct =>
          cases expected with
          | collection actual elementType =>
              simp only [Bool.and_eq_true, beq_iff_eq] at direct
              rcases direct with ⟨⟨actualEquality, elementsChecked⟩, _⟩
              subst actual
              exact .collection
                (checkSchemaElements_sound_of
                  (fun element membership elementChecked =>
                    inductionHypothesis element membership elementChecked)
                  elementsChecked)
          | base sort => simp at direct
          | arrow domain codomain => simp at direct
          | multiBinder type => simp at direct
      | inr authored =>
          obtain ⟨rule, ruleMember, ruleChecked⟩ := authored
          generalize elementTypeEquation :
            bareCollectionElementType? rule collectionType expected = result
              at ruleChecked
          cases result with
          | none => simp at ruleChecked
          | some elementType =>
            rw [bareCollectionElementType?_eq_some_iff] at elementTypeEquation
            rcases elementTypeEquation with
              ⟨expectedEquality, parameterName, parameterShape⟩
            subst expected
            exact .collectionConstructor ruleMember parameterShape
              (checkSchemaElements_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                (by
                  have pair : checkSchemaElements domains language free bound elements elementType = true ∧
                      checkSchemaRest free collectionType elementType rest = true := by
                    simpa only [Bool.and_eq_true] using ruleChecked
                  exact pair.1))

/-- Every successful homogeneous element-spine check is a derivation in the
sole authored typing relation. -/
theorem checkSchemaElements_sound
    {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (checked : checkSchemaElements domains language free bound elements
      elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  exact checkSchemaElements_sound_of
    (fun _element _membership elementChecked =>
      checkSchemaType_sound elementChecked)
    checked

mutual
  /-- Every declaratively typed object pattern is accepted by the executable
  checker.  The object premise excludes schema-only substitutions and open
  collection tails, exactly matching the executable carrier. -/
  theorem checkSchemaType_complete_of_object
      {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
      (typed : HasType language free bound pattern expected)
      (object : isObjectPattern pattern = true) :
      checkSchemaType domains language free bound pattern expected = true := by
    cases typed with
    | bvar lookup => simp [checkSchemaType, lookup]
    | fvar lookup => simp [checkSchemaType, lookup]
    | @constructor bound rule arguments ruleMember notBare argumentsTyped =>
        simp only [isObjectPattern] at object
        have notBareChecked : usesBareCollection? rule = false := by
          apply Bool.eq_false_of_not_eq_true
          intro bareChecked
          exact notBare
            ((usesBareCollection?_eq_true_iff rule).mp bareChecked)
        simp only [checkSchemaType, List.any_eq_true]
        exact ⟨rule, ruleMember, by
          simp [notBareChecked,
            checkSchemaArguments_complete_of_objects (domains := domains)
              argumentsTyped object]⟩
    | @lambda bound binder body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        simpa [checkSchemaType] using
          checkSchemaType_complete_of_object (domains := domains) bodyTyped object
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        simpa [checkSchemaType] using
          checkSchemaType_complete_of_object (domains := domains) bodyTyped object
    | subst bodyTyped replacementTyped =>
        simp [isObjectPattern] at object
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        have elementsChecked :=
          checkSchemaElements_complete_of_objects (domains := domains) elementsTyped object.2
        have closed : rest = none := by cases rest <;> simp_all
        simp [checkSchemaType, closed, checkSchemaRest, elementsChecked]
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType ruleMember parameterShape elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        have elementTypeEquation :
            bareCollectionElementType? rule collectionType
                (.base rule.category) = some elementType :=
          (bareCollectionElementType?_eq_some_iff rule collectionType
            (.base rule.category) elementType).mpr
              ⟨rfl, parameterName, parameterShape⟩
        have elementsChecked :=
          checkSchemaElements_complete_of_objects (domains := domains) elementsTyped object.2
        have closed : rest = none := by cases rest <;> simp_all
        simp only [checkSchemaType, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨rule, ruleMember, by
          rw [elementTypeEquation]
          simp only [closed, checkSchemaRest, elementsChecked, Bool.and_self]⟩

  /-- Completeness companion for ordered constructor arguments. -/
  theorem checkSchemaArguments_complete_of_objects
      {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (objects : isObjectPatternList arguments = true) :
      checkSchemaArguments domains language free bound arguments parameters = true := by
    cases typed with
    | nil => rfl
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkSchemaArguments, parameterType, Bool.and_eq_true]
        exact ⟨⟨
          (matchesParameterRepresentation?_eq_true_iff
            parameter argument).mpr representation,
          checkSchemaType_complete_of_object (domains := domains) argumentTyped objects.1⟩,
          checkSchemaArguments_complete_of_objects (domains := domains)
            argumentsTyped objects.2⟩

  /-- Completeness companion for collection elements. -/
  theorem checkSchemaElements_complete_of_objects
      {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (objects : isObjectPatternList elements = true) :
      checkSchemaElements domains language free bound elements elementType = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [checkSchemaElements, Bool.and_eq_true]
        exact ⟨checkSchemaType_complete_of_object (domains := domains) elementTyped objects.1,
          checkSchemaElements_complete_of_objects (domains := domains) elementsTyped objects.2⟩
end

/-- On object patterns, executable checking is exactly the sole declarative
typing relation rather than a parallel approximation. -/
theorem checkSchemaType_eq_true_iff
    {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (object : isObjectPattern pattern = true) :
    checkSchemaType domains language free bound pattern expected = true ↔
      HasType language free bound pattern expected :=
  ⟨checkSchemaType_sound, fun typed =>
    checkSchemaType_complete_of_object (domains := domains) typed object⟩


/-- Every admitted substitution uses the actual body and replacement typing
checks, rather than the object checker's schema rejection. -/
theorem checkSchemaType_subst {domains : List TypeExpr} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {body replacement : Pattern}
    {domain expected : TypeExpr} (declared : domain ∈ domains)
    (bodyChecked : checkSchemaType domains language free (domain :: bound) body expected = true)
    (replacementChecked : checkSchemaType domains language free bound replacement domain = true) :
    checkSchemaType domains language free bound (.subst body replacement) expected = true := by
  exact List.any_eq_true.mpr ⟨domain, declared, by simp [bodyChecked, replacementChecked]⟩

/-- Collect every nested type in an authored type expression. -/
def typeVocabulary : TypeExpr → List TypeExpr
  | type@(.base _) => [type]
  | type@(.arrow domain codomain) => type :: (typeVocabulary domain ++ typeVocabulary codomain)
  | type@(.multiBinder domain) => type :: typeVocabulary domain
  | type@(.collection _ element) => type :: typeVocabulary element

/-- The finite schema domain vocabulary is data extracted from declarations,
metavariable types, and the actual bound typing context. -/
def declaredDomains (language : LanguageDef) (rule : RewriteRule)
    (bound : List TypeExpr) : List TypeExpr :=
  ((language.types.map fun category => TypeExpr.base category.name) ++
    (language.terms.flatMap fun declaration =>
      (.base declaration.category :: declaration.params.filterMap parameterType?).flatMap typeVocabulary) ++
    (rule.typeContext.map Prod.snd).flatMap typeVocabulary ++
    bound.flatMap typeVocabulary).eraseDups

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SchemaTyping
