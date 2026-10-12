import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

open Mettapedia.OSLF.Framework

/-!
# Executable typing of authored source schemas

This checker derives typing from the original authored declarations. Open
collection tails are schema metadata, retained without an object-pattern
admission condition. Explicit substitutions require an intermediate type;
this finite bidirectional profile reports them as unresolved rather than
claiming that rejection decides their independent typing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
  def substitutionFree : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => substitutionFreeList arguments
    | .lambda _ body | .multiLambda _ _ body => substitutionFree body
    | .subst _ _ => false
    | .collection _ elements _ => substitutionFreeList elements

  def substitutionFreeList : List Pattern → Bool
    | [] => true
    | first :: remaining => substitutionFree first && substitutionFreeList remaining
end

mutual
  /-- Check one raw pattern against an expected type in the exact authored
  free and bound contexts. -/
  def schemaCheckHasType (language : LanguageDef) (free : FreeTypeContext)
      (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Bool :=
    match pattern with
    | .bvar index => bound[index]? == some expected
    | .fvar name => free name == some expected
    | .apply constructor arguments =>
        language.terms.any fun rule =>
          rule.label == constructor &&
            expected == .base rule.category &&
            !usesBareCollection? rule &&
            schemaCheckArguments language free bound arguments rule.params
    | .lambda _ body =>
        match expected with
        | .arrow domain codomain =>
            schemaCheckHasType language free (domain :: bound) body codomain
        | _ => false
    | .multiLambda arity _ body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            schemaCheckHasType language free
              (List.replicate arity domain ++ bound) body codomain
        | _ => false
    | .subst _ _ => false
    | .collection collectionType elements _ =>
        let direct :=
          match expected with
          | .collection actual elementType =>
              actual == collectionType &&
                schemaCheckElements language free bound elements elementType
          | _ => false
        let authored := language.terms.any fun rule =>
          match bareCollectionElementType? rule collectionType expected with
          | some elementType =>
              schemaCheckElements language free bound elements elementType
          | none => false
        direct || authored

  /-- Ordered argument-spine checker compiled from the authored parameter
  list. -/
  def schemaCheckArguments (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → List TermParam → Bool
    | [], [] => true
    | argument :: arguments, parameter :: parameters =>
        match parameterType? parameter with
        | some expected =>
            matchesParameterRepresentation? parameter argument &&
              schemaCheckHasType language free bound argument expected &&
              schemaCheckArguments language free bound arguments parameters
        | none => false
    | _, _ => false

  /-- Pointwise checker for collection elements. -/
  def schemaCheckElements (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      List Pattern → TypeExpr → Bool
    | [], _ => true
    | element :: elements, elementType =>
        schemaCheckHasType language free bound element elementType &&
          schemaCheckElements language free bound elements elementType
end

/-- Soundness of the argument-spine checker, assuming soundness for every
immediate argument pattern. -/
theorem schemaCheckArguments_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (argumentSound : ∀ argument ∈ arguments, ∀ expected,
      schemaCheckHasType language free bound argument expected = true →
        HasType language free bound argument expected)
    (checked : schemaCheckArguments language free bound
      arguments parameters = true) :
    ArgumentsHaveTypes language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters =>
          simp [schemaCheckArguments] at checked
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => simp [schemaCheckArguments] at checked
      | cons parameter parameters =>
          cases parameterTypeEquation : parameterType? parameter with
          | none =>
              simp [schemaCheckArguments, parameterTypeEquation] at checked
          | some expected =>
              simp only [schemaCheckArguments, parameterTypeEquation,
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
theorem schemaCheckElements_sound_of
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (elementSound : ∀ element ∈ elements,
      schemaCheckHasType language free bound element elementType = true →
        HasType language free bound element elementType)
    (checked : schemaCheckElements language free bound
      elements elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  induction elements with
  | nil => exact .nil bound elementType
  | cons element elements inductionHypothesis =>
      simp only [schemaCheckElements, Bool.and_eq_true] at checked
      exact .cons
        (elementSound element (by simp) checked.1)
        (inductionHypothesis
          (fun other membership otherChecked =>
            elementSound other (by simp [membership]) otherChecked)
          checked.2)

/-- Every successful executable check is a derivation in the sole declarative
typing relation authored by `LanguageDef`. -/
theorem schemaCheckHasType_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (checked : schemaCheckHasType language free bound pattern expected = true) :
    HasType language free bound pattern expected := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      simp only [schemaCheckHasType, beq_iff_eq] at checked
      exact .bvar checked
  | hfvar name =>
      simp only [schemaCheckHasType, beq_iff_eq] at checked
      exact .fvar checked
  | happly constructor arguments inductionHypothesis =>
      simp only [schemaCheckHasType, List.any_eq_true, Bool.and_eq_true,
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
        (schemaCheckArguments_sound_of
          (fun argument membership argumentExpected argumentChecked =>
            inductionHypothesis argument membership argumentChecked)
          argumentsChecked)
  | hlambda binder body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          exact .lambda (inductionHypothesis checked)
      | base sort => simp [schemaCheckHasType] at checked
      | multiBinder type => simp [schemaCheckHasType] at checked
      | collection collectionType elementType =>
          simp [schemaCheckHasType] at checked
  | hmultiLambda arity binders body inductionHypothesis =>
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              exact .multiLambda (inductionHypothesis checked)
          | base sort => simp [schemaCheckHasType] at checked
          | arrow first second => simp [schemaCheckHasType] at checked
          | collection collectionType elementType =>
              simp [schemaCheckHasType] at checked
      | base sort => simp [schemaCheckHasType] at checked
      | multiBinder type => simp [schemaCheckHasType] at checked
      | collection collectionType elementType =>
          simp [schemaCheckHasType] at checked
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [schemaCheckHasType] at checked
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [schemaCheckHasType,
        Bool.or_eq_true, List.any_eq_true] at checked
      cases checked with
      | inl direct =>
          cases expected with
          | collection actual elementType =>
              simp only [Bool.and_eq_true, beq_iff_eq] at direct
              rcases direct with ⟨actualEquality, elementsChecked⟩
              subst actual
              exact .collection
                (schemaCheckElements_sound_of
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
              (schemaCheckElements_sound_of
                (fun element membership elementChecked =>
                  inductionHypothesis element membership elementChecked)
                ruleChecked)

/-- Every successful homogeneous element-spine check is a derivation in the
sole authored typing relation. -/
theorem schemaCheckElements_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern}
    {elementType : TypeExpr}
    (checked : schemaCheckElements language free bound elements
      elementType = true) :
    ElementsHaveType language free bound elements elementType := by
  exact schemaCheckElements_sound_of
    (fun _element _membership elementChecked =>
      schemaCheckHasType_sound elementChecked)
    checked

mutual
  /-- Every independently typed substitution-free source schema is accepted.
  Collection tails remain in the source and do not require object admission. -/
  theorem schemaCheckHasType_complete
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
      (typed : HasType language free bound pattern expected)
      (object : substitutionFree pattern = true) :
      schemaCheckHasType language free bound pattern expected = true := by
    cases typed with
    | bvar lookup => simp [schemaCheckHasType, lookup]
    | fvar lookup => simp [schemaCheckHasType, lookup]
    | @constructor bound rule arguments ruleMember notBare argumentsTyped =>
        simp only [substitutionFree] at object
        have notBareChecked : usesBareCollection? rule = false := by
          apply Bool.eq_false_of_not_eq_true
          intro bareChecked
          exact notBare
            ((usesBareCollection?_eq_true_iff rule).mp bareChecked)
        simp only [schemaCheckHasType, List.any_eq_true]
        exact ⟨rule, ruleMember, by
          simp [notBareChecked,
            schemaCheckArguments_complete
              argumentsTyped object]⟩
    | @lambda bound binder body domain codomain bodyTyped =>
        simp only [substitutionFree] at object
        simpa [schemaCheckHasType] using
          schemaCheckHasType_complete bodyTyped object
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simp only [substitutionFree] at object
        simpa [schemaCheckHasType] using
          schemaCheckHasType_complete bodyTyped object
    | subst bodyTyped replacementTyped =>
        simp [substitutionFree] at object
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simp only [substitutionFree] at object
        have elementsChecked :=
          schemaCheckElements_complete elementsTyped object
        simp [schemaCheckHasType, elementsChecked]
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType ruleMember parameterShape elementsTyped =>
        simp only [substitutionFree] at object
        have elementTypeEquation :
            bareCollectionElementType? rule collectionType
                (.base rule.category) = some elementType :=
          (bareCollectionElementType?_eq_some_iff rule collectionType
            (.base rule.category) elementType).mpr
              ⟨rfl, parameterName, parameterShape⟩
        have elementsChecked :=
          schemaCheckElements_complete elementsTyped object
        simp only [schemaCheckHasType, Bool.or_eq_true,
          List.any_eq_true]
        exact Or.inr ⟨rule, ruleMember, by
          rw [elementTypeEquation]
          exact elementsChecked⟩

  /-- Completeness companion for ordered constructor arguments. -/
  theorem schemaCheckArguments_complete
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (objects : substitutionFreeList arguments = true) :
      schemaCheckArguments language free bound arguments parameters = true := by
    cases typed with
    | nil => rfl
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        simp only [substitutionFreeList, Bool.and_eq_true] at objects
        simp only [schemaCheckArguments, parameterType, Bool.and_eq_true]
        exact ⟨⟨
          (matchesParameterRepresentation?_eq_true_iff
            parameter argument).mpr representation,
          schemaCheckHasType_complete argumentTyped objects.1⟩,
          schemaCheckArguments_complete
            argumentsTyped objects.2⟩

  /-- Completeness companion for collection elements. -/
  theorem schemaCheckElements_complete
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (objects : substitutionFreeList elements = true) :
      schemaCheckElements language free bound elements elementType = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [substitutionFreeList, Bool.and_eq_true] at objects
        simp only [schemaCheckElements, Bool.and_eq_true]
        exact ⟨schemaCheckHasType_complete elementTyped objects.1,
          schemaCheckElements_complete elementsTyped objects.2⟩
end

/-- On substitution-free authored schemas, executable checking is exactly
the independent declarative typing relation. -/
theorem schemaCheckHasType_iff
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr}
    (object : substitutionFree pattern = true) :
    schemaCheckHasType language free bound pattern expected = true ↔
      HasType language free bound pattern expected :=
  ⟨schemaCheckHasType_sound, fun typed =>
    schemaCheckHasType_complete typed object⟩


/-- A false result decides ill typing only inside the classified schema
profile. An unclassified substitution remains an explicit unresolved result. -/
def schemaTypingStatus? (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) : Option Bool :=
  if substitutionFree source then some (schemaCheckHasType language free bound source expected) else none

theorem schemaTypingStatus?_some_iff (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) (accepted : Bool) :
    schemaTypingStatus? language free bound source expected = some accepted ↔
      substitutionFree source = true ∧ schemaCheckHasType language free bound source expected = accepted := by
  simp [schemaTypingStatus?]

theorem substitution_status_unresolved (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (body replacement : Pattern) (expected : TypeExpr) :
    schemaTypingStatus? language free bound (.subst body replacement) expected = none := rfl

end Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
