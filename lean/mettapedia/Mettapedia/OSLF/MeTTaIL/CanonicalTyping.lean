import Mettapedia.OSLF.MeTTaIL.CanonicalMatching
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Canonical forms keep typing

A permutation of an unordered collection's elements, or a re-presentation of a set by the same
elements, changes no type: collection typing is pointwise, and every other node keeps its head
and binder metadata. Hence canonical forms of well-sorted open patterns are well-sorted, and
canonical captures of a typed assignment are typed.

- `BagStep.hasType`, `BagStep.openPatternWellSorted`: one step keeps typing;
- `openPatternWellSorted_canon`: canonical forms keep well-sortedness;
- `typedAssignment_canon`: canonical captures keep the declared sorts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef} {free : FreeTypeContext}

theorem elementsHaveType_iff {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr} :
    ElementsHaveType language free bound elements elementType ↔
      ∀ element ∈ elements, HasType language free bound element elementType := by
  induction elements with
  | nil => exact ⟨fun _ _ member => absurd member List.not_mem_nil, fun _ => .nil _ _⟩
  | cons element rest ih =>
    constructor
    · rintro (_ | ⟨head, tail⟩) item member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact head
      · exact ih.mp tail item inRest
    · intro all
      exact .cons (all _ (.head _)) (ih.mpr fun item member => all item (.tail _ member))

theorem matchesParameterRepresentation_bagStep {parameter : TermParam} {left right : Pattern}
    (step : BagStep left right) (matched : MatchesParameterRepresentation parameter left) :
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

private theorem argumentsHaveTypes_middle {bound : List TypeExpr} {argument changed : Pattern}
    (stepped : BagStep argument changed)
    (typed : ∀ {type : TypeExpr}, HasType language free bound argument type → HasType language free bound changed type) :
    ∀ {before after : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound (before ++ argument :: after) parameters →
      ArgumentsHaveTypes language free bound (before ++ changed :: after) parameters
  | [], after, parameters, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons (matchesParameterRepresentation_bagStep stepped representation) parameterType (typed head) tail
  | item :: before, after, parameters, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons representation parameterType head (argumentsHaveTypes_middle stepped typed tail)

/-- **One permutation keeps typing.** -/
theorem BagStep.hasType {left right : Pattern} (step : BagStep left right) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}, HasType language free bound left type →
      HasType language free bound right type := by
  induction step with
  | permute _ permutation =>
    intro bound type typed
    cases typed with
    | collection elements =>
      exact .collection (elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp elements item (permutation.mem_iff.mpr member))
    | collectionConstructor declared parameters elements =>
      exact .collectionConstructor declared parameters (elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp elements item (permutation.mem_iff.mpr member))
  | members same =>
    intro bound type typed
    cases typed with
    | collection elements =>
      exact .collection (elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp elements item ((same item).mpr member))
    | collectionConstructor declared parameters elements =>
      exact .collectionConstructor declared parameters (elementsHaveType_iff.mpr fun item member =>
        elementsHaveType_iff.mp elements item ((same item).mpr member))
  | apply inner ih =>
    intro bound type typed
    cases typed with
    | constructor declared notBare arguments =>
      exact .constructor declared notBare (argumentsHaveTypes_middle inner ih arguments)
  | lambda _ ih =>
    intro bound type typed
    cases typed with
    | lambda body => exact .lambda (ih body)
  | multiLambda _ ih =>
    intro bound type typed
    cases typed with
    | multiLambda body => exact .multiLambda (ih body)
  | substBody _ ih =>
    intro bound type typed
    cases typed with
    | subst body replacement => exact .subst (ih body) replacement
  | substReplacement _ ih =>
    intro bound type typed
    cases typed with
    | subst body replacement => exact .subst body (ih replacement)
  | @element kind before after element changed rest _ ih =>
    intro bound type typed
    have pointwise : ∀ {elementType : TypeExpr},
        ElementsHaveType language free bound (before ++ element :: after) elementType →
        ElementsHaveType language free bound (before ++ changed :: after) elementType := fun elements =>
      elementsHaveType_iff.mpr fun item member => by
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · exact elementsHaveType_iff.mp elements item (by simp [inBefore])
        · exact ih (elementsHaveType_iff.mp elements _ (by simp))
        · exact elementsHaveType_iff.mp elements item (by simp [inAfter])
    cases typed with
    | collection elements => exact .collection (pointwise elements)
    | collectionConstructor declared parameters elements =>
      exact .collectionConstructor declared parameters (pointwise elements)

private theorem listAll_middle {f : Pattern → Bool} {before after : List Pattern} {x y : Pattern} (same : f x = f y) :
    (before ++ x :: after).all f = (before ++ y :: after).all f := by
  simp [List.all_append, same]

theorem BagStep.binderMetadata_eq {left right : Pattern} (step : BagStep left right) :
    left.hasCanonicalBinderMetadata = right.hasCanonicalBinderMetadata := by
  have listForm : ∀ items : List Pattern,
      Pattern.hasCanonicalBinderMetadataList items = items.all Pattern.hasCanonicalBinderMetadata := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [Pattern.hasCanonicalBinderMetadataList, ih]
  induction step with
  | permute _ permutation =>
    simp only [Pattern.hasCanonicalBinderMetadata, listForm]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item (permutation.mem_iff.mpr member),
        fun all item member => all item (permutation.mem_iff.mp member)⟩)
  | members same =>
    simp only [Pattern.hasCanonicalBinderMetadata, listForm]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item ((same item).mpr member),
        fun all item member => all item ((same item).mp member)⟩)
  | apply _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle ih
  | lambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | multiLambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substBody _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substReplacement _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | element _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle ih

theorem BagStep.objectPattern_eq {left right : Pattern} (step : BagStep left right) :
    WellSorted.isObjectPattern left = WellSorted.isObjectPattern right := by
  have listForm : ∀ items : List Pattern, WellSorted.isObjectPatternList items = items.all WellSorted.isObjectPattern := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [WellSorted.isObjectPatternList, ih]
  induction step with
  | permute _ permutation =>
    simp only [WellSorted.isObjectPattern, listForm]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item (permutation.mem_iff.mpr member),
        fun all item member => all item (permutation.mem_iff.mp member)⟩)
  | members same =>
    simp only [WellSorted.isObjectPattern, listForm]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact
      ⟨fun all item member => all item ((same item).mpr member),
        fun all item member => all item ((same item).mp member)⟩)
  | apply _ ih => simp only [WellSorted.isObjectPattern, listForm]; exact listAll_middle ih
  | lambda _ ih => simp only [WellSorted.isObjectPattern, ih]
  | multiLambda _ ih => simp only [WellSorted.isObjectPattern, ih]
  | substBody _ ih => simp only [WellSorted.isObjectPattern]
  | substReplacement _ ih => simp only [WellSorted.isObjectPattern]
  | element _ ih => simp only [WellSorted.isObjectPattern, listForm]; rw [listAll_middle ih]

/-- **One permutation keeps well-sortedness.** -/
theorem BagStep.openPatternWellSorted {left right : Pattern} (step : BagStep left right)
    {bound : List TypeExpr} {type : TypeExpr} (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  obtain ⟨typed, metadata, object, scope⟩ := sorted
  exact ⟨step.hasType typed, step.binderMetadata_eq ▸ metadata, step.objectPattern_eq ▸ object,
    by unfold ScopeSafeAt at scope ⊢; rw [← step.wellScoped]; exact scope⟩

theorem openPatternWellSorted_of_eqvGen {left right : Pattern} (related : Relation.EqvGen BagStep left right)
    {bound : List TypeExpr} {type : TypeExpr} (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  have chain := eqvGen_reflTransGen related
  clear related
  induction chain with
  | refl => exact sorted
  | tail _ step ih => exact step.openPatternWellSorted ih

/-- **Canonical forms keep well-sortedness.** -/
theorem openPatternWellSorted_canon {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (sorted : OpenPatternWellSorted language free bound type pattern) :
    OpenPatternWellSorted language free bound type (canon pattern) :=
  openPatternWellSorted_of_eqvGen (to_canon pattern) sorted

theorem hasType_of_chain {left right : Pattern} (chain : Relation.ReflTransGen BagStep left right)
    {bound : List TypeExpr} {type : TypeExpr} (typed : HasType language free bound left type) :
    HasType language free bound right type := by
  induction chain with
  | refl => exact typed
  | tail _ step ih => exact step.hasType ih

theorem objectPattern_of_chain {left right : Pattern} (chain : Relation.ReflTransGen BagStep left right) :
    isObjectPattern left = isObjectPattern right := by
  induction chain with
  | refl => rfl
  | tail _ step ih => rw [ih, step.objectPattern_eq]

theorem hasType_canon {pattern : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound pattern type) : HasType language free bound (canon pattern) type :=
  hasType_of_chain (eqvGen_reflTransGen (to_canon pattern)) typed

theorem isObjectPattern_canon (pattern : Pattern) : isObjectPattern (canon pattern) = isObjectPattern pattern :=
  (objectPattern_of_chain (eqvGen_reflTransGen (to_canon pattern))).symm

/-- **Canonical captures keep the declared sorts.** -/
theorem typedAssignment_canon {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {assignment : ScopedRuleMatching.Assignment} (typed : GeneralPremise.TypedAssignment environment context assignment) :
    GeneralPremise.TypedAssignment environment context (canonAssignment assignment) := by
  obtain ⟨sorts, objects⟩ := typed
  refine ⟨fun name value member => ?_, fun name value member => ?_⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, bodyTyped⟩ :=
      sorts name₀ value₀ inOriginal
    exact ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, hasType_canon bodyTyped⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    simp only [canonValue, isObjectPattern_canon]
    exact objects name₀ value₀ inOriginal

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
