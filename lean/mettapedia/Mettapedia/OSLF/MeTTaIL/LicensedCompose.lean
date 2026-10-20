import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Composing licensed occurrences

A licensed occurrence in a source, followed by a licensed occurrence in a replacement of its
focus, is a licensed occurrence in the source with that replacement (`Licensed.compose`), when
the replacement has the representation the outer path expects. Addresses, contexts and typing
frames concatenate (`SiteData.compose`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralTypedSites.SiteData

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- An occurrence inside the focus of another. -/
def compose (outer inner : SiteData) : SiteData where
  address := outer.address ++ inner.address
  context := outer.context.comp inner.context
  focus := inner.focus
  focusBound := inner.focusBound
  focusType := inner.focusType
  typingFrames := outer.typingFrames ++ inner.typingFrames

theorem here_compose (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (inner : SiteData) :
    (here bound expected source).compose inner = inner := by
  cases inner; rfl

end Mettapedia.OSLF.MeTTaIL.GeneralTypedSites.SiteData

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open WellSorted

private theorem take_replace {α : Type} (items : List α) (index : Nat) (item : α) (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1)).take index = items.take index := by
  have length : (items.take index).length = index := by simp; omega
  rw [List.take_append, length, Nat.sub_self, List.take_zero, List.append_nil, List.take_take, Nat.min_self]

private theorem drop_replace {α : Type} (items : List α) (index : Nat) (item : α) (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1)).drop (index + 1) = items.drop (index + 1) := by
  have length : (items.take index).length = index := by simp; omega
  rw [List.drop_append, length, List.drop_eq_nil_of_le (by simp), List.nil_append,
    show index + 1 - index = 1 by omega]
  rfl

private theorem getElem?_replace {α : Type} (items : List α) (index : Nat) (item : α) (within : index < items.length) :
    (items.take index ++ item :: items.drop (index + 1))[index]? = some item := by
  have length : (items.take index).length = index := by simp; omega
  rw [List.getElem?_append_right (by omega), length, Nat.sub_self]
  rfl

private theorem objects_replace {items : List Pattern} {index : Nat} {item : Pattern}
    (objects : isObjectPatternList items = true) (object : isObjectPattern item = true) :
    isObjectPatternList (items.take index ++ item :: items.drop (index + 1)) = true := by
  have all : ∀ items : List Pattern, isObjectPatternList items = items.all isObjectPattern := by
    intro items; induction items with
    | nil => rfl
    | cons head tail ih => simp [isObjectPatternList, ih]
  rw [all] at objects ⊢
  simp only [List.all_append, List.all_cons, object, Bool.true_and, Bool.and_eq_true]
  rw [List.all_eq_true] at objects ⊢
  rw [List.all_eq_true]
  exact ⟨fun x member => objects x (List.mem_of_mem_take member),
    fun x member => objects x (List.mem_of_mem_drop member)⟩

namespace Licensed

variable {language : LanguageDef} {free : FreeTypeContext} {permissions : OperationalPermissions}

/-- **Composing licensed occurrences.** -/
theorem compose {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {outer : SiteData}
    (licensed : Licensed language free permissions bound expected source outer) :
    ∀ {replacement : Pattern} {inner : SiteData},
      outer.acceptsReplacementRepresentation language replacement = true →
      Licensed language free permissions outer.focusBound outer.focusType replacement inner →
      Licensed language free permissions bound expected (outer.context.fill replacement) (outer.compose inner) := by
  induction licensed with
  | here _ _ _ =>
    intro replacement inner _ innerLicensed
    rw [SiteData.here_compose]
    exact innerLicensed
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary argumentsTyped objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    intro replacement innerSite accepts innerSiteLicensed
    have declarationAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapApplication,
      replacementRepresentations?, declarationAt, Option.bind_some, parameterSelected, Bool.and_eq_true] at accepts
    have represented := (matchesParameterRepresentation?_eq_true_iff _ _).mp accepts.1
    have composed := ih accepts.2 innerSiteLicensed
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have site_eq : (inner.compose innerSite).wrapApplication declaration rule.label
        (arguments.take index ++ inner.context.fill replacement :: arguments.drop (index + 1)) index =
        (inner.wrapApplication declaration rule.label arguments index).compose innerSite := by
      simp only [SiteData.compose, SiteData.wrapApplication, OneHoleContext.comp, take_replace _ _ _ within,
        drop_replace _ _ _ within, List.cons_append]
    rw [← site_eq]
    show Licensed _ _ _ _ _ (Pattern.apply rule.label
      (arguments.take index ++ inner.context.fill replacement :: arguments.drop (index + 1))) _
    exact .application declared ordinary
      (replace_argument argumentsTyped parameterSelected parameterTyped represented composed.source_typed)
      (objects_replace objects composed.source_object) (getElem?_replace _ _ _ within) parameterSelected parameterTyped
      permitted composed
  | @lambda bound binder body domain codomain inner enabled innerLicensed ih =>
    intro replacement innerSite accepts innerSiteLicensed
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapLambda, replacementRepresentations?] at accepts
    have composed := ih accepts innerSiteLicensed
    have site_eq : (inner.compose innerSite).wrapLambda binder domain = (inner.wrapLambda binder domain).compose innerSite := by
      simp only [SiteData.compose, SiteData.wrapLambda, OneHoleContext.comp, List.cons_append]
    rw [← site_eq]
    exact .lambda enabled composed
  | @multiLambda bound arity binders body domain codomain inner enabled innerLicensed ih =>
    intro replacement innerSite accepts innerSiteLicensed
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapMultiLambda,
      replacementRepresentations?] at accepts
    have composed := ih accepts innerSiteLicensed
    have site_eq : (inner.compose innerSite).wrapMultiLambda arity binders domain =
        (inner.wrapMultiLambda arity binders domain).compose innerSite := by
      simp only [SiteData.compose, SiteData.wrapMultiLambda, OneHoleContext.comp, List.cons_append]
    rw [← site_eq]
    exact .multiLambda enabled composed
  | @directCollection bound kind elements index element elementType inner permitted elementsTyped objects selected
      innerLicensed ih =>
    intro replacement innerSite accepts innerSiteLicensed
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapCollection,
      replacementRepresentations?] at accepts
    have composed := ih accepts innerSiteLicensed
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have site_eq : (inner.compose innerSite).wrapCollection (.directCollection kind) kind
        (elements.take index ++ inner.context.fill replacement :: elements.drop (index + 1)) index =
        (inner.wrapCollection (.directCollection kind) kind elements index).compose innerSite := by
      simp only [SiteData.compose, SiteData.wrapCollection, OneHoleContext.comp, take_replace _ _ _ within,
        drop_replace _ _ _ within, List.cons_append]
    rw [← site_eq]
    show Licensed _ _ _ _ _ (Pattern.collection kind
      (elements.take index ++ inner.context.fill replacement :: elements.drop (index + 1)) none) _
    exact .directCollection permitted (replace_element elementsTyped selected composed.source_typed)
      (objects_replace objects composed.source_object) (getElem?_replace _ _ _ within) composed
  | @authoredCollection bound rule declaration parameterName kind elements index element elementType inner
      declared shape permitted elementsTyped objects selected innerLicensed ih =>
    intro replacement innerSite accepts innerSiteLicensed
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapCollection,
      replacementRepresentations?] at accepts
    have composed := ih accepts innerSiteLicensed
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have site_eq : (inner.compose innerSite).wrapCollection (.authoredCollection declaration) kind
        (elements.take index ++ inner.context.fill replacement :: elements.drop (index + 1)) index =
        (inner.wrapCollection (.authoredCollection declaration) kind elements index).compose innerSite := by
      simp only [SiteData.compose, SiteData.wrapCollection, OneHoleContext.comp, take_replace _ _ _ within,
        drop_replace _ _ _ within, List.cons_append]
    rw [← site_eq]
    show Licensed _ _ _ _ _ (Pattern.collection kind
      (elements.take index ++ inner.context.fill replacement :: elements.drop (index + 1)) none) _
    exact .authoredCollection declared shape permitted (replace_element elementsTyped selected composed.source_typed)
      (objects_replace objects composed.source_object) (getElem?_replace _ _ _ within) composed

end Licensed

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
