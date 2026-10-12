import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Licensed

open Mettapedia.OSLF.Framework

/-!
# Complete coverage of independently typed source-schema zippers

Every substitution-free authored schema occurrence justified by the existing
`TypedAt` relation is represented with its exact source context, including an
open collection tail. The retained declaration indices are derived from the
actual grammar lookup rather than supplied as a separate site vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem substitutionFreeList_member {elements : List Pattern} {element : Pattern}
    (objects : substitutionFreeList elements = true) (member : element ∈ elements) :
    substitutionFree element = true := by
  induction elements with
  | nil => cases member
  | cons first rest ih =>
    simp only [substitutionFreeList, Bool.and_eq_true] at objects
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ objects.1
    · exact ih objects.2 later

/-- Every independently typed and structurally permitted source schema occurrence
admits a licensed witness with the same exact zipper, focus and binder sorts. -/
theorem typedAt_licensed {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {focus : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {expected focusType : TypeExpr}
    (selected : TypedAt language free focus context bound expected focusBound focusType)
    (objects : substitutionFree (context.fill focus) = true)
    (permitted : permitsContext permissions context = true) :
    ∃ site : SiteData,
      Licensed language free permissions bound expected (context.fill focus) site ∧
      site.context = context ∧ site.focus = focus ∧
      site.focusBound = focusBound ∧ site.focusType = focusType := by
  revert objects permitted
  induction selected with
  | here typed =>
    intro objects permitted
    exact ⟨SiteData.here _ _ _, .here permitted objects typed, rfl, rfl, rfl, rfl⟩
  | @application rule before after inner bound focusBound parameterType focusType
      beforeParams afterParams parameter declared ordinary typed shape length parameterTyped innerTyped ih =>
    intro objects permitted
    change substitutionFreeList (before ++ inner.fill focus :: after) = true at objects
    simp only [permitsContext, Bool.and_eq_true] at permitted
    have innerObject := substitutionFreeList_member (element := inner.fill focus) objects (by simp)
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ := ih innerObject permitted.2
    obtain ⟨declaration, declarationAt⟩ := List.mem_iff_getElem?.mp declared
    have actualDeclared := List.mk_mem_zipIdx_iff_getElem?.mpr declarationAt
    have argumentAt : (before ++ inner.fill focus :: after)[before.length]? = some (inner.fill focus) := by
      simp
    have parameterAt : rule.params[before.length]? = some parameter := by
      rw [shape, ← length]
      simp
    refine ⟨site.wrapApplication declaration rule.label (before ++ inner.fill focus :: after) before.length,
      .application actualDeclared ordinary typed objects argumentAt parameterAt parameterTyped
        ((permitsArgument_spec _ _ _).mp permitted.1) licensed, ?_, focusEq, boundEq, typeEq⟩
    simp [SiteData.wrapApplication, contextEq]
  | @lambda binder inner bound focusBound domain codomain focusType innerTyped ih =>
    intro objects permitted
    change substitutionFree (inner.fill focus) = true at objects
    simp only [permitsContext, Bool.and_eq_true] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ := ih objects permitted.2
    exact ⟨site.wrapLambda binder domain, .lambda permitted.1 licensed,
      congrArg (OneHoleContext.lambda binder) contextEq, focusEq, boundEq, typeEq⟩
  | @multiLambda arity binders inner bound focusBound domain codomain focusType innerTyped ih =>
    intro objects permitted
    change substitutionFree (inner.fill focus) = true at objects
    simp only [permitsContext, Bool.and_eq_true] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ := ih objects permitted.2
    exact ⟨site.wrapMultiLambda arity binders domain, .multiLambda permitted.1 licensed,
      congrArg (OneHoleContext.multiLambda arity binders) contextEq, focusEq, boundEq, typeEq⟩
  | substBody _ _ _ =>
    intro _ permitted
    simp [permitsContext] at permitted
  | substReplacement _ _ _ =>
    intro _ permitted
    simp [permitsContext] at permitted
  | @collection kind before after inner rest bound focusBound elementType focusType typed innerTyped ih =>
    intro objects permitted
    change substitutionFreeList (before ++ inner.fill focus :: after) = true at objects
    simp only [permitsContext, Bool.and_eq_true, decide_eq_true_eq] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ :=
      ih (substitutionFreeList_member objects (by simp)) permitted.2
    have elementAt : (before ++ inner.fill focus :: after)[before.length]? = some (inner.fill focus) := by simp
    refine ⟨site.wrapSchemaCollection (.directCollection kind) kind
      (before ++ inner.fill focus :: after) before.length rest,
      .directCollection permitted.1 typed objects elementAt licensed,
      ?_, focusEq, boundEq, typeEq⟩
    simp [SiteData.wrapSchemaCollection, contextEq]
  | @collectionConstructor rule parameterName kind before after inner rest bound focusBound
      elementType focusType declared shape typed innerTyped ih =>
    intro objects permitted
    change substitutionFreeList (before ++ inner.fill focus :: after) = true at objects
    simp only [permitsContext, Bool.and_eq_true, decide_eq_true_eq] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ :=
      ih (substitutionFreeList_member objects (by simp)) permitted.2
    obtain ⟨declaration, declarationAt⟩ := List.mem_iff_getElem?.mp declared
    have actualDeclared := List.mk_mem_zipIdx_iff_getElem?.mpr declarationAt
    have elementAt : (before ++ inner.fill focus :: after)[before.length]? = some (inner.fill focus) := by simp
    refine ⟨site.wrapSchemaCollection (.authoredCollection declaration) kind
      (before ++ inner.fill focus :: after) before.length rest,
      .authoredCollection actualDeclared shape permitted.1 typed objects elementAt licensed,
      ?_, focusEq, boundEq, typeEq⟩
    simp [SiteData.wrapSchemaCollection, contextEq]

/-- The full structural schema profile grants every actual substitution-free
zipper. No separate context-permission oracle is required. -/
theorem all_context_permitted (focus : Pattern) (context : OneHoleContext)
    (classified : substitutionFree (context.fill focus) = true) :
    permitsContext .all context = true := by
  induction context with
  | hole => rfl
  | apply constructor before inner after ih =>
      have innerClassified := substitutionFreeList_member
        (show substitutionFreeList (before ++ inner.fill focus :: after) = true from classified)
        (show inner.fill focus ∈ before ++ inner.fill focus :: after by simp)
      simpa [permitsContext, OperationalPermissions.all, OperationalPermissions.permitsArgument]
        using ih innerClassified
  | lambda binder inner ih =>
      simpa [permitsContext, OperationalPermissions.all] using ih classified
  | multiLambda arity binders inner ih =>
      simpa [permitsContext, OperationalPermissions.all] using ih classified
  | substBody inner replacement ih =>
      cases classified
  | substReplacement body inner ih =>
      cases classified
  | collection kind before inner after rest ih =>
      have innerClassified := substitutionFreeList_member
        (show substitutionFreeList (before ++ inner.fill focus :: after) = true from classified)
        (show inner.fill focus ∈ before ++ inner.fill focus :: after by simp)
      have permitted : kind ∈ OperationalPermissions.all.collectionKinds := by
        cases kind <;> decide +kernel
      simpa [permitsContext, permitted] using ih innerClassified

end Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
