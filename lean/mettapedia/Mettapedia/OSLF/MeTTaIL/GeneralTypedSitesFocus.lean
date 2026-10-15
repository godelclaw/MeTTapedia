import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts

/-!
# Ordinary object and canonical focus readouts

Independent occurrence licensing retains the object representation of its
focus. A canonical caller therefore licenses a fully sorted local source
with the actual complete binder context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open WellSorted

theorem focus_object {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    isObjectPattern site.focus = true := by
  induction licensed <;> assumption

theorem focus_sorted {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (canonical : source.hasCanonicalBinderMetadata = true) :
    OpenPatternWellSorted language free site.focusBound site.focusType site.focus := by
  refine ⟨licensed.focus_typed, ?_, licensed.focus_object, licensed.focus_typed.isWellScopedAt⟩
  apply Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts.canonical_redex site.context site.focus
  rw [licensed.source_eq]
  exact canonical

#print axioms focus_sorted

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
