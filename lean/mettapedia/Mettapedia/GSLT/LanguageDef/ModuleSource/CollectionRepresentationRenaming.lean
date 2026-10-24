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

theorem retained_collection_representation_rename (symbols : LanguageDefSymbolMap)
    (injective : Function.Injective symbols.constructor) (language : LanguageDef) :
    (retainSharedCollectionLabels { language with terms := language.terms.map (mapGrammarRule symbols) }).terms =
      (retainSharedCollectionLabels language).terms.map (mapGrammarRule symbols) := by
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
    dsimp only
    rw [shared]
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
end Mettapedia.GSLT.LanguageDef.ModuleSource
