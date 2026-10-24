import Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceAdmission

/-!
# Independently licensed typed occurrences of authored object terms

The judgment follows actual grammar declarations and actual source children.
Operational permission is separate from structural occurrence selection and
from typing. Declaration positions record every relevant typing alternative;
the final binder context records exact sorts, rather than only binder depth.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open WellSorted

theorem take_selected_drop {α : Type} {elements : List α} {index : Nat} {element : α}
    (selected : elements[index]? = some element) :
    elements.take index ++ element :: elements.drop (index + 1) = elements := by
  have bounds := (List.getElem?_eq_some_iff.mp selected).1
  have actual := List.getElem?_eq_getElem bounds
  rw [selected] at actual
  have elementEq := Option.some.inj actual
  rw [elementEq, List.getElem_cons_drop bounds]
  exact List.take_append_drop index elements

/-- A licensed ordinary object occurrence. The constructors refer only to
authored typing, source positions and permission data, not to a site generator. -/
inductive Licensed (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) :
    List TypeExpr → TypeExpr → Pattern → SiteData → Prop where
  | here {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} :
      permissions.enabled = true → isObjectPattern source = true →
      HasType language free bound source expected →
      Licensed language free permissions bound expected source (SiteData.here bound expected source)
  | application {bound : List TypeExpr} {rule : GrammarRule} {declaration index : Nat}
      {arguments : List Pattern} {argument : Pattern} {parameter : TermParam}
      {parameterType : TypeExpr} {inner : SiteData} :
      (rule, declaration) ∈ language.terms.zipIdx → ¬ UsesBareCollection rule →
      ArgumentsHaveTypes language free bound arguments rule.params →
      isObjectPatternList arguments = true →
      arguments[index]? = some argument → rule.params[index]? = some parameter →
      parameterType? parameter = some parameterType →
      (permissions.allConstructorArguments = true ∨
        (rule.label, index) ∈ permissions.constructorArguments) →
      Licensed language free permissions bound parameterType argument inner →
      Licensed language free permissions bound (.base rule.category) (.apply rule.label arguments)
        (inner.wrapApplication declaration rule.label arguments index)
  | lambda {bound : List TypeExpr} {binder : Option String} {body : Pattern}
      {domain codomain : TypeExpr} {inner : SiteData} :
      permissions.underLambda = true →
      Licensed language free permissions (domain :: bound) codomain body inner →
      Licensed language free permissions bound (.arrow domain codomain) (.lambda binder body)
        (inner.wrapLambda binder domain)
  | multiLambda {bound : List TypeExpr} {arity : Nat} {binders : List String} {body : Pattern}
      {domain codomain : TypeExpr} {inner : SiteData} :
      permissions.underMultiLambda = true →
      Licensed language free permissions (List.replicate arity domain ++ bound) codomain body inner →
      Licensed language free permissions bound (.arrow (.multiBinder domain) codomain)
        (.multiLambda arity binders body) (inner.wrapMultiLambda arity binders domain)
  | directCollection {bound : List TypeExpr} {kind : CollType} {elements : List Pattern}
      {index : Nat} {element : Pattern} {elementType : TypeExpr} {inner : SiteData} :
      kind ∈ permissions.collectionKinds →
      ElementsHaveType language free bound elements elementType →
      isObjectPatternList elements = true → elements[index]? = some element →
      Licensed language free permissions bound elementType element inner →
      Licensed language free permissions bound (.collection kind elementType)
        (.collection kind elements none)
        (inner.wrapCollection (.directCollection kind) kind elements index)
  | authoredCollection {bound : List TypeExpr} {rule : GrammarRule} {declaration : Nat}
      {parameterName : String} {kind : CollType} {elements : List Pattern}
      {index : Nat} {element : Pattern} {elementType : TypeExpr} {inner : SiteData} :
      (rule, declaration) ∈ language.terms.zipIdx →
      rule.bareParams = [.simple parameterName (.collection kind elementType)] →
      kind ∈ permissions.collectionKinds →
      ElementsHaveType language free bound elements elementType →
      isObjectPatternList elements = true → elements[index]? = some element →
      Licensed language free permissions bound elementType element inner →
      Licensed language free permissions bound (.base rule.category)
        (.collection kind elements none)
        (inner.wrapCollection (.authoredCollection declaration) kind elements index)

namespace Licensed

variable {language : LanguageDef} {free : FreeTypeContext} {permissions : OperationalPermissions}
  {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}

theorem enabled (licensed : Licensed language free permissions bound expected source site) :
    permissions.enabled = true := by
  induction licensed <;> assumption

theorem source_typed (licensed : Licensed language free permissions bound expected source site) :
    HasType language free bound source expected := by
  induction licensed with
  | here _ _ typed => exact typed
  | application declared ordinary arguments _ _ _ _ _ _ _ =>
      exact .constructor (List.fst_mem_of_mem_zipIdx declared) ordinary arguments
  | lambda _ _ ih => exact .lambda ih
  | multiLambda _ _ ih => exact .multiLambda ih
  | directCollection _ elements _ _ _ _ => exact .collection elements
  | authoredCollection declared shape _ elements _ _ _ _ =>
      exact .collectionConstructor (List.fst_mem_of_mem_zipIdx declared) shape elements

theorem source_object (licensed : Licensed language free permissions bound expected source site) :
    isObjectPattern source = true := by
  induction licensed with
  | here _ object _ => exact object
  | application _ _ _ objects _ _ _ _ _ _ => exact objects
  | lambda _ _ ih => exact ih
  | multiLambda _ _ ih => exact ih
  | directCollection _ _ objects _ _ _ => simpa [isObjectPattern] using objects
  | authoredCollection _ _ _ _ objects _ _ _ => simpa [isObjectPattern] using objects

theorem source_eq (licensed : Licensed language free permissions bound expected source site) :
    site.context.fill site.focus = source := by
  induction licensed with
  | here _ _ _ => rfl
  | application _ _ _ _ selected _ _ _ _ ih =>
      simp only [SiteData.wrapApplication, OneHoleContext.fill, ih]
      rw [take_selected_drop selected]
  | lambda _ _ ih => simpa [SiteData.wrapLambda, OneHoleContext.fill] using ih
  | multiLambda _ _ ih => simpa [SiteData.wrapMultiLambda, OneHoleContext.fill] using ih
  | directCollection _ _ _ selected _ ih =>
      simp only [SiteData.wrapCollection, OneHoleContext.fill, ih]
      rw [take_selected_drop selected]
  | authoredCollection _ _ _ _ _ selected _ ih =>
      simp only [SiteData.wrapCollection, OneHoleContext.fill, ih]
      rw [take_selected_drop selected]

theorem typedAt (licensed : Licensed language free permissions bound expected source site) :
    TypedAt language free site.focus site.context bound expected site.focusBound site.focusType := by
  induction licensed with
  | here _ _ typed => exact .here typed
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
      have paramBounds := (List.getElem?_eq_some_iff.mp parameterSelected).1
      have argBounds := (List.getElem?_eq_some_iff.mp selected).1
      dsimp only [SiteData.wrapApplication]
      apply TypedAt.application (List.fst_mem_of_mem_zipIdx declared) ordinary
      · simp only [innerLicensed.source_eq, take_selected_drop selected]
        exact typed
      · exact (take_selected_drop parameterSelected).symm
      · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt paramBounds),
          Nat.min_eq_left (Nat.le_of_lt argBounds)]
      · exact parameterTyped
      · exact ih
  | lambda _ _ ih => exact .lambda ih
  | multiLambda _ _ ih => exact .multiLambda ih
  | directCollection _ typed _ selected innerLicensed ih =>
      dsimp only [SiteData.wrapCollection]
      apply TypedAt.collection
      · simp only [innerLicensed.source_eq, take_selected_drop selected]
        exact typed
      · exact ih
  | authoredCollection declared shape _ typed _ selected innerLicensed ih =>
      dsimp only [SiteData.wrapCollection]
      apply TypedAt.collectionConstructor (List.fst_mem_of_mem_zipIdx declared) shape
      · simp only [innerLicensed.source_eq, take_selected_drop selected]
        exact typed
      · exact ih

theorem focus_typed (licensed : Licensed language free permissions bound expected source site) :
    HasType language free site.focusBound site.focus site.focusType := licensed.typedAt.focus_typed

theorem ambient_retained (licensed : Licensed language free permissions bound expected source site) :
    ∃ binderPrefix, site.focusBound = binderPrefix ++ bound := licensed.typedAt.ambient_suffix

theorem selects (licensed : Licensed language free permissions bound expected source site) :
    Selects site.focus site.context source := by
  rw [← licensed.source_eq]
  exact Selects.of_fill site.context site.focus

theorem permitted (licensed : Licensed language free permissions bound expected source site) :
    permissions.permitsContext site.context = true := by
  induction licensed with
  | here enabled _ _ => exact enabled
  | application _ _ _ _ selected _ _ permitted _ ih =>
    have bounds := (List.getElem?_eq_some_iff.mp selected).1
    simp only [SiteData.wrapApplication, OperationalPermissions.permitsContext, List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt bounds)]
    exact (Bool.and_eq_true _ _).mpr ⟨(permitsArgument_spec _ _ _).mpr permitted, ih⟩
  | lambda permitted _ ih => exact (Bool.and_eq_true _ _).mpr ⟨permitted, ih⟩
  | multiLambda permitted _ ih => exact (Bool.and_eq_true _ _).mpr ⟨permitted, ih⟩
  | directCollection permitted _ _ _ _ ih =>
    simpa [SiteData.wrapCollection, OperationalPermissions.permitsContext, permitted] using ih
  | authoredCollection _ _ permitted _ _ _ _ ih =>
    simpa [SiteData.wrapCollection, OperationalPermissions.permitsContext, permitted] using ih

theorem address_eq (licensed : Licensed language free permissions bound expected source site) :
    site.address = contextAddress site.context := by
  induction licensed with
  | here _ _ _ => rfl
  | application _ _ _ _ selected _ _ _ _ ih =>
    have bounds := (List.getElem?_eq_some_iff.mp selected).1
    simp only [SiteData.wrapApplication, contextAddress, List.length_take, ih,
      Nat.min_eq_left (Nat.le_of_lt bounds)]
  | lambda _ _ ih => exact congrArg (List.cons 0) ih
  | multiLambda _ _ ih => exact congrArg (List.cons 0) ih
  | directCollection _ _ _ selected _ ih =>
    have bounds := (List.getElem?_eq_some_iff.mp selected).1
    simp only [SiteData.wrapCollection, contextAddress, List.length_take, ih,
      Nat.min_eq_left (Nat.le_of_lt bounds)]
  | authoredCollection _ _ _ _ _ selected _ ih =>
    have bounds := (List.getElem?_eq_some_iff.mp selected).1
    simp only [SiteData.wrapCollection, contextAddress, List.length_take, ih,
      Nat.min_eq_left (Nat.le_of_lt bounds)]

theorem binder_depth (licensed : Licensed language free permissions bound expected source site) :
    site.focusBound.length = bound.length +
      Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress.binderCount site.context := by
  induction licensed with
  | here _ _ _ => simp [SiteData.here, Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress.binderCount]
  | application _ _ _ _ _ _ _ _ _ ih => exact ih
  | lambda _ _ ih =>
    simpa [SiteData.wrapLambda, Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress.binderCount,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
  | multiLambda _ _ ih =>
    simpa [SiteData.wrapMultiLambda, Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress.binderCount,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
  | directCollection _ _ _ _ _ ih => exact ih
  | authoredCollection _ _ _ _ _ _ _ ih => exact ih

theorem replace (licensed : Licensed language free permissions bound expected source site)
    (target : Pattern) (compatible : RepresentationCompatible site.focus target)
    (replacement : HasType language free site.focusBound target site.focusType) :
    HasType language free bound (site.context.fill target) expected :=
  licensed.typedAt.replace compatible replacement

end Licensed

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
