import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.Framework

/-!
# Whole-source coverage and retained schema-typing diagnostics

Every ordinary raw occurrence of an independently typed, substitution-free
authored source receives its real typing descent. This includes occurrences
inside binders and open collection schemas. The supplied expected type is
retained: this result does not infer an unbounded pool of possible carriers.
An unclassified explicit substitution remains unresolved, even when it has
an independent typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem every_typed_source_has_root {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (typed : HasType language free bound source expected)
    (classified : substitutionFree source = true) :
    SiteData.here bound expected source ∈ generate language free .all bound expected source :=
  generate_complete (.here rfl classified typed)

/-- The raw source zipper determines the generated occurrence; the complete
focus context and carrier are recovered from its actual typing derivation. -/
theorem every_typed_source_occurrence {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {source focus : Pattern}
    {context : OneHoleContext}
    (typed : HasType language free bound source expected)
    (classified : substitutionFree source = true)
    (selected : Selects focus context source) :
    ∃ site ∈ generate language free .all bound expected source,
      site.context = context ∧ site.focus = focus ∧
      TypedAt language free site.focus site.context bound expected site.focusBound site.focusType := by
  have sourceTyped : HasType language free bound (context.fill focus) expected :=
    selected.fill_eq.symm ▸ typed
  obtain ⟨focusBound, focusType, descended⟩ := hasType_typedAt context sourceTyped
  have sourceClassified : substitutionFree (context.fill focus) = true :=
    selected.fill_eq.symm ▸ classified
  obtain ⟨site, licensed, contextEq, focusEq, _, _⟩ := typedAt_licensed descended sourceClassified
    (all_context_permitted focus context sourceClassified)
  refine ⟨site, ?_, contextEq, focusEq, ?_⟩
  · rw [← selected.fill_eq]
    exact generate_complete licensed
  · exact licensed.typedAt

structure Enumeration where
  sites : List SiteData
  typingStatus : Option Bool
  deriving Repr

def generateWithStatus (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : Enumeration :=
  ⟨generate language free permissions bound expected source,
    schemaTypingStatus? language free bound source expected⟩

theorem typed_source_status {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} (typed : HasType language free bound source expected)
    (classified : substitutionFree source = true) :
    (generateWithStatus language free permissions bound expected source).typingStatus = some true := by
  simp [generateWithStatus, schemaTypingStatus?, classified, schemaCheckHasType_complete typed classified]

theorem unclassified_source_status (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (unclassified : substitutionFree source = false) :
    (generateWithStatus language free permissions bound expected source).typingStatus = none := by
  simp [generateWithStatus, schemaTypingStatus?, unclassified]

/-- A pending substitution can be genuinely typed while its finite typing
classification remains unresolved. An empty catalogue is not a denial. -/
theorem typed_substitution_is_unresolved {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {body replacement : Pattern} {domain codomain : TypeExpr}
    (bodyTyped : HasType language free (domain :: bound) body codomain)
    (replacementTyped : HasType language free bound replacement domain) :
    HasType language free bound (.subst body replacement) codomain ∧
      (generateWithStatus language free .all bound codomain (.subst body replacement)).typingStatus = none ∧
      (generateWithStatus language free .all bound codomain (.subst body replacement)).sites = [] := by
  refine ⟨.subst bodyTyped replacementTyped, rfl, ?_⟩
  simp only [generateWithStatus, generate.eq_def, substitutionFree, Bool.false_eq_true,
    and_false, false_and, ↓reduceIte]

end Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
