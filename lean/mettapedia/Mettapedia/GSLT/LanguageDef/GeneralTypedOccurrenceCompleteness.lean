import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-!
# Coverage of existing typed occurrence descent

The independent licensed judgment covers every existing `TypedAt` derivation
whose structural path is operationally permitted and whose source is an
object term. This comparison rules out silently omitting a typing alternative
when constructor labels or bare collection sorts are ambiguous.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open WellSorted

theorem objectList_member {elements : List Pattern} {element : Pattern}
    (objects : isObjectPatternList elements = true) (member : element ∈ elements) :
    isObjectPattern element = true := by
  induction elements with
  | nil => cases member
  | cons first rest ih =>
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ objects.1
    · exact ih objects.2 later

/-- Every independently typed and operationally permitted object occurrence
admits a licensed witness with the same exact zipper, focus and binder sorts. -/
theorem typedAt_licensed {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {focus : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {expected focusType : TypeExpr}
    (selected : TypedAt language free focus context bound expected focusBound focusType)
    (objects : isObjectPattern (context.fill focus) = true)
    (permitted : permissions.permitsContext context = true) :
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
    change isObjectPatternList (before ++ inner.fill focus :: after) = true at objects
    simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at permitted
    have innerObject := objectList_member (element := inner.fill focus) objects (by simp)
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
    change isObjectPattern (inner.fill focus) = true at objects
    simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ := ih objects permitted.2
    exact ⟨site.wrapLambda binder domain, .lambda permitted.1 licensed,
      congrArg (OneHoleContext.lambda binder) contextEq, focusEq, boundEq, typeEq⟩
  | @multiLambda arity binders inner bound focusBound domain codomain focusType innerTyped ih =>
    intro objects permitted
    change isObjectPattern (inner.fill focus) = true at objects
    simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at permitted
    obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ := ih objects permitted.2
    exact ⟨site.wrapMultiLambda arity binders domain, .multiLambda permitted.1 licensed,
      congrArg (OneHoleContext.multiLambda arity binders) contextEq, focusEq, boundEq, typeEq⟩
  | substBody _ _ _ =>
    intro _ permitted
    simp [OperationalPermissions.permitsContext] at permitted
  | substReplacement _ _ _ =>
    intro _ permitted
    simp [OperationalPermissions.permitsContext] at permitted
  | @collection kind before after inner rest bound focusBound elementType focusType typed innerTyped ih =>
    intro objects permitted
    cases rest with
    | some _ => simp [OperationalPermissions.permitsContext] at permitted
    | none =>
      change isObjectPatternList (before ++ inner.fill focus :: after) = true at objects
      simp only [OperationalPermissions.permitsContext, Option.isNone_none, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at permitted
      obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ :=
        ih (objectList_member objects (by simp)) permitted.2
      have elementAt : (before ++ inner.fill focus :: after)[before.length]? = some (inner.fill focus) := by simp
      refine ⟨site.wrapCollection (.directCollection kind) kind
        (before ++ inner.fill focus :: after) before.length,
        .directCollection permitted.1 typed objects elementAt licensed,
        ?_, focusEq, boundEq, typeEq⟩
      simp [SiteData.wrapCollection, contextEq]
  | @collectionConstructor rule parameterName kind before after inner rest bound focusBound
      elementType focusType declared shape typed innerTyped ih =>
    intro objects permitted
    cases rest with
    | some _ => simp [OperationalPermissions.permitsContext] at permitted
    | none =>
      change isObjectPatternList (before ++ inner.fill focus :: after) = true at objects
      simp only [OperationalPermissions.permitsContext, Option.isNone_none, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at permitted
      obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ :=
        ih (objectList_member objects (by simp)) permitted.2
      obtain ⟨declaration, declarationAt⟩ := List.mem_iff_getElem?.mp declared
      have actualDeclared := List.mk_mem_zipIdx_iff_getElem?.mpr declarationAt
      have elementAt : (before ++ inner.fill focus :: after)[before.length]? = some (inner.fill focus) := by simp
      refine ⟨site.wrapCollection (.authoredCollection declaration) kind
        (before ++ inner.fill focus :: after) before.length,
        .authoredCollection actualDeclared shape permitted.1 typed objects elementAt licensed,
        ?_, focusEq, boundEq, typeEq⟩
      simp [SiteData.wrapCollection, contextEq]

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
