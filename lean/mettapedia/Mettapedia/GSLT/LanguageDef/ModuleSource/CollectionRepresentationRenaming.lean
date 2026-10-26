import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentation
import Mettapedia.GSLT.LanguageDef.StructuralCategory
/-! # Renaming preserves collection representation selection

The actual declaration pass commutes with the existing grammar-row action
when constructor names are renamed injectively. Sort maps need not be
injective for this particular representation-selection law. A map that
identifies constructor names has a separate obligation.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem collectionParameterKind_map (symbols : LanguageDefSymbolMap) (rule : GrammarRule) :
    collectionParameterKind (mapGrammarRule symbols rule) = collectionParameterKind rule := by
  cases rule with
  | mk label category params syntaxRows policy algebra mode =>
    cases params with
    | nil => rfl
    | cons head tail =>
      cases tail with
      | cons =>
        cases head with
        | simple name type => cases type <;> rfl
        | abstractionNamed => rfl
        | multiAbstractionNamed => rfl
      | nil =>
        cases head with
        | simple name type => cases type <;> rfl
        | abstractionNamed => rfl
        | multiAbstractionNamed => rfl

theorem mentionsCollection_mapTypeExpr (symbols : LanguageDefSymbolMap) (kind : CollType)
    (type : TypeExpr) :
    (mapTypeExpr symbols type).mentionsCollection kind = type.mentionsCollection kind := by
  induction type <;> simp_all [mapTypeExpr, TypeExpr.mentionsCollection]

theorem mentionsCollection_mapTermParam (symbols : LanguageDefSymbolMap) (kind : CollType)
    (parameter : TermParam) :
    (mapTermParam symbols parameter).typeExpr.mentionsCollection kind =
      parameter.typeExpr.mentionsCollection kind := by
  cases parameter <;> simp [mapTermParam, TermParam.typeExpr, mentionsCollection_mapTypeExpr]

theorem collectionAlgebraCandidate_map (symbols : LanguageDefSymbolMap)
    (injective : Function.Injective symbols.constructor) (rule : GrammarRule)
    (binaryLabels : List String) :
    collectionAlgebraCandidate (mapGrammarRule symbols rule) (binaryLabels.map symbols.constructor) =
      collectionAlgebraCandidate rule binaryLabels := by
  have contains : (binaryLabels.map symbols.constructor).contains (symbols.constructor rule.label) =
      binaryLabels.contains rule.label := by
    apply Bool.eq_iff_iff.mpr
    simp [List.mem_map, injective.eq_iff]
  unfold collectionAlgebraCandidate
  change ((binaryLabels.map symbols.constructor).contains (symbols.constructor rule.label) &&
      (rule.algebra?.map (StructuralMorphism.mapCollectionAlgebra symbols.constructor)).isNone) = _
  rw [contains]
  congr 1
  cases rule.algebra? <;> rfl

theorem otherCollectionParameter_map (symbols : LanguageDefSymbolMap)
    (injective : Function.Injective symbols.constructor) (language : LanguageDef)
    (rule : GrammarRule) (kind : CollType) :
    otherCollectionParameter {language with terms := language.terms.map (mapGrammarRule symbols)}
        (mapGrammarRule symbols rule) kind = otherCollectionParameter language rule kind := by
  unfold otherCollectionParameter
  rw [List.any_map]
  congr 1
  funext other
  change ((symbols.constructor other.label != symbols.constructor rule.label) &&
      (other.params.map (mapTermParam symbols)).any
        (fun field => field.typeExpr.mentionsCollection kind)) = _
  have different : (symbols.constructor other.label != symbols.constructor rule.label) =
      (other.label != rule.label) := by
    apply Bool.eq_iff_iff.mpr
    simp [injective.eq_iff]
  rw [different, List.any_map]
  congr 1
  congr 1
  funext parameter
  exact mentionsCollection_mapTermParam symbols kind parameter


theorem retained_collection_representation_rename (symbols : LanguageDefSymbolMap)
    (injective : Function.Injective symbols.constructor) (language : LanguageDef)
    (binaryLabels : List String := []) :
    (retainSharedCollectionLabels
      {language with terms := language.terms.map (mapGrammarRule symbols)}
      (binaryLabels.map symbols.constructor)).terms =
      (retainSharedCollectionLabels language binaryLabels).terms.map (mapGrammarRule symbols) := by
  simp only [retainSharedCollectionLabels, List.map_map]
  apply List.map_congr_left
  intro rule _
  simp only [Function.comp_apply, collectionParameterKind_map]
  cases kindFound : collectionParameterKind rule with
  | none => rfl
  | some kind =>
    have shared : (language.terms.map (mapGrammarRule symbols)).any (fun other =>
          other.label != (mapGrammarRule symbols rule).label && collectionParameterKind other == some kind) =
        language.terms.any (fun other => other.label != rule.label && collectionParameterKind other == some kind) := by
      simp only [List.any_map]
      congr 1
      funext other
      change (symbols.constructor other.label != symbols.constructor rule.label &&
          collectionParameterKind (mapGrammarRule symbols other) == some kind) = _
      rw [collectionParameterKind_map]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp [injective.eq_iff]
    have candidate := collectionAlgebraCandidate_map symbols injective rule binaryLabels
    have data := otherCollectionParameter_map symbols injective language rule kind
    dsimp only
    rw [shared, candidate, data]
    split <;> rfl

theorem bareKind_renameUnitReferences (old new : String) (rule : GrammarRule) :
    Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind (renameUnitReferences old new rule) =
      Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind rule := rfl

/-- Transporting unit references keeps the normalizer's kind/uniqueness
selection and flattening authority. The selected unit names follow the same
symbol action as the declarations, including absent units. -/
theorem declared_algebras_unit_rename (old new : String) (language : LanguageDef) :
    Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared
        { language with terms := language.terms.map (renameUnitReferences old new) } =
      (Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared language).map
        (fun law => { law with unit := law.unit.map (renameName old new) }) := by
  simp only [Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared, List.map_filterMap]
  congr 1
  funext kind
  have selected :
      (language.terms.map (renameUnitReferences old new)).filter
          (fun rule => Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind rule == some kind) =
        (language.terms.filter
          (fun rule => Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind rule == some kind)).map
          (renameUnitReferences old new) := by
    simp only [List.filter_map, Function.comp_def, bareKind_renameUnitReferences]
  rw [selected]
  cases found : language.terms.filter
      (fun rule => Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind rule == some kind) with
  | nil => rfl
  | cons rule rest =>
    cases rest with
    | cons => rfl
    | nil =>
      cases algebra : rule.algebra? with
      | none => simp [renameUnitReferences, algebra]
      | some value =>
        cases flatten : value.flatten <;>
          simp [renameUnitReferences, StructuralMorphism.mapCollectionAlgebra, algebra, flatten]

namespace RenamingControls

def carrier (label : String) : GrammarRule :=
  { label, category := "Number", params := [.simple "xs" (.collection .hashBag (.base "Number"))],
    syntaxPattern := [] }

def language : LanguageDef :=
  { name := "TwoOperations", types := [TypeDecl.plain "Number"],
    terms := [carrier "Sum", carrier "Product"], equations := [], rewrites := [] }

def identify : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with constructor := fun _ => "Merged" }

theorem identifying_names_does_not_commute :
    (retainSharedCollectionLabels
      { language with terms := language.terms.map (mapGrammarRule identify) }).terms ≠
      (retainSharedCollectionLabels language).terms.map (mapGrammarRule identify) := by decide

end RenamingControls
#print axioms collectionParameterKind_map
#print axioms mentionsCollection_mapTypeExpr
#print axioms mentionsCollection_mapTermParam
#print axioms collectionAlgebraCandidate_map
#print axioms otherCollectionParameter_map
#print axioms retained_collection_representation_rename
#print axioms bareKind_renameUnitReferences
#print axioms declared_algebras_unit_rename
#print axioms RenamingControls.identifying_names_does_not_commute
end Mettapedia.GSLT.LanguageDef.ModuleSource
