import Mettapedia.OSLF.MeTTaIL.WrapperLaws
import Mettapedia.OSLF.MeTTaIL.LawNormalTyping

/-!
# Wrapper laws keep typing

A singleton collection of a flattening kind is its element, and the empty one is the declared unit.
The two laws keep the type of a term exactly when every such collection is a term of its bare
constructor, typed at that constructor's sort: then the element has the same sort (the constructor is
homogeneous) and so has the unit. A collection typed at a collection type instead, as the argument of a
parameter of collection type, would change its type when its wrapper collapses. `WrappersTyped` asks
that no parameter other than a bare constructor's own mention a collection of a flattening kind
(`NoLawCollections`), and that the bare constructors are homogeneous with units of their sort.

- `WrapperStep.hasType`: one wrapper step, left to right, keeps the type of an object term at a type
  without collections of a flattening kind.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A type that mentions no collection of a flattening kind. -/
def NoLawCollections (laws : List Laws) : TypeExpr → Prop
  | .base _ => True
  | .arrow domain codomain => NoLawCollections laws domain ∧ NoLawCollections laws codomain
  | .multiBinder domain => NoLawCollections laws domain
  | .collection kind element => lawFor laws kind = none ∧ NoLawCollections laws element

/-- The language types its wrapper laws: bare constructors of flattening kinds are homogeneous, with a
unit of their sort, and no other parameter mentions a collection of a flattening kind. -/
structure WrappersTyped (laws : List Laws) (language : LanguageDef) : Prop where
  homogeneous : ∀ law kind, lawFor laws kind = some law → ∀ rule ∈ language.terms, ∀ name element,
    rule.params = [.simple name (.collection kind element)] → element = .base rule.category
  units : ∀ law kind, lawFor laws kind = some law → ∀ label, law.unit = some label →
    ∀ rule ∈ language.terms, ∀ name element, rule.params = [.simple name (.collection kind element)] →
      ∃ unitRule ∈ language.terms, unitRule.label = label ∧ unitRule.params = [] ∧ unitRule.category = rule.category
  bareElements : ∀ rule ∈ language.terms, ∀ name kind element,
    rule.params = [.simple name (.collection kind element)] → NoLawCollections laws element
  parameters : ∀ rule ∈ language.terms, ¬ UsesBareCollection rule → ∀ parameter ∈ rule.params, ∀ type,
    parameterType? parameter = some type → NoLawCollections laws type

variable {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}

theorem matchesParameterRepresentation_wrapper {parameter : TermParam} {left right : Pattern}
    (step : WrapperStep laws left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
    obtain ⟨body, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp matched
    cases step with
    | lambda _ => exact (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mpr ⟨_, rfl⟩
  | multiAbstractionNamed binders name type =>
    cases step with
    | multiLambda _ =>
      rename_i binders' _ _ _
      cases binders' with
      | nil => trivial
      | cons => simp [MatchesParameterRepresentation] at matched
    | _ => simp [MatchesParameterRepresentation] at matched

/-- Arguments of a constructor whose parameters mention no collection of a flattening kind. -/
private theorem argumentsHaveTypes_middle {bound : List TypeExpr} {argument changed : Pattern}
    (stepped : WrapperStep laws argument changed)
    (typed : ∀ {type : TypeExpr}, NoLawCollections laws type →
      HasType language free bound argument type → HasType language free bound changed type) :
    ∀ {before after : List Pattern} {parameters : List TermParam},
      (∀ parameter ∈ parameters, ∀ type, parameterType? parameter = some type → NoLawCollections laws type) →
      ArgumentsHaveTypes language free bound (before ++ argument :: after) parameters →
      ArgumentsHaveTypes language free bound (before ++ changed :: after) parameters
  | [], after, parameters, noLaw, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons (matchesParameterRepresentation_wrapper stepped representation) parameterType
        (typed (noLaw _ (.head _) _ parameterType) head) tail
  | item :: before, after, parameters, noLaw, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons representation parameterType head
        (argumentsHaveTypes_middle stepped typed (fun parameter member => noLaw parameter (.tail _ member)) tail)

/-- **One wrapper step keeps the type of an object term**, at a type without collections of a
flattening kind. -/
theorem WrapperStep.hasType (admission : WrappersTyped laws language) {left right : Pattern}
    (step : WrapperStep laws left right) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}, isObjectPattern left = true → NoLawCollections laws type →
      HasType language free bound left type → HasType language free bound right type := by
  induction step with
  | @singleton kind law element found =>
    intro bound type _ noLaw typed
    cases typed with
    | collection _ => exact absurd noLaw.1 (by rw [found]; simp)
    | @collectionConstructor _ rule parameterName _ _ _ elementType declared parameters elements =>
      have same := admission.homogeneous law kind found rule declared parameterName elementType
        ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
      subst same
      exact elementsHaveType_iff.mp elements element (.head _)
  | @empty kind law label found unit =>
    intro bound type _ noLaw typed
    cases typed with
    | collection _ => exact absurd noLaw.1 (by rw [found]; simp)
    | @collectionConstructor _ rule parameterName _ _ _ elementType declared parameters _ =>
      obtain ⟨unitRule, unitDeclared, unitLabel, unitParameters, unitCategory⟩ :=
        admission.units law kind found label unit rule declared parameterName elementType
          ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
      rw [← unitCategory, ← unitLabel]
      exact .constructor unitDeclared (by
        rintro ⟨_, _, _, same⟩
        have raw := ((GrammarRule.bareParams_cons_iff _ _ _).mp same).2
        rw [unitParameters] at raw
        cases raw)
        (by rw [unitParameters]; exact .nil)
  | @apply label before after argument changed inner ih =>
    intro bound type object _ typed
    cases typed with
    | @constructor _ rule arguments declared notBare typedArguments =>
      have objects : isObjectPattern argument = true := by
        simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
        exact object _ (by simp)
      exact .constructor declared notBare (argumentsHaveTypes_middle inner
        (fun noLaw typedArgument => ih objects noLaw typedArgument) (admission.parameters rule declared notBare)
        typedArguments)
  | lambda _ ih =>
    intro bound type object noLaw typed
    cases typed with
    | lambda body => exact .lambda (ih (by simpa [isObjectPattern] using object) noLaw.2 body)
  | multiLambda _ ih =>
    intro bound type object noLaw typed
    cases typed with
    | multiLambda body => exact .multiLambda (ih (by simpa [isObjectPattern] using object) noLaw.2 body)
  | substBody _ _ => intro _ _ object; simp [isObjectPattern] at object
  | substReplacement _ _ => intro _ _ object; simp [isObjectPattern] at object
  | @element kind before after element changed rest _ ih =>
    intro bound type object noLaw typed
    have objectElement : isObjectPattern element = true := by
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      exact object.2 _ (by simp)
    have pointwise : ∀ {elementType : TypeExpr}, NoLawCollections laws elementType →
        ElementsHaveType language free bound (before ++ element :: after) elementType →
        ElementsHaveType language free bound (before ++ changed :: after) elementType := fun noLawElement elements =>
      elementsHaveType_iff.mpr fun item member => by
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · exact elementsHaveType_iff.mp elements item (by simp [inBefore])
        · exact ih objectElement noLawElement (elementsHaveType_iff.mp elements _ (by simp))
        · exact elementsHaveType_iff.mp elements item (by simp [inAfter])
    cases typed with
    | collection elements => exact .collection (pointwise noLaw.2 elements)
    | @collectionConstructor _ rule parameterName _ _ _ elementType declared parameters elements =>
      exact .collectionConstructor declared parameters
        (pointwise (admission.bareElements rule declared parameterName kind elementType
          ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2) elements)

end Mettapedia.OSLF.MeTTaIL.Wrappers
