import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceEquationSourceTyping

/-!
# Typed canonical sources at every licensed site

The complete caller judgment descends through the actual licensed zipper.
Local binder sorts come from that typing descent; scope follows from typing,
and canonical display metadata follows from the selected caller subterm.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts
open WellSorted

theorem focus_object {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    isObjectPattern site.focus = true := by
  induction licensed <;> assumption

theorem focus_open {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (typed : OpenPatternWellSorted language free bound expected source) :
    OpenPatternWellSorted language free site.focusBound site.focusType site.focus := by
  exact ⟨licensed.focus_typed,
    canonical_redex site.context site.focus (licensed.source_eq.symm ▸ typed.2.1),
    licensed.focus_object, licensed.focus_typed.isWellScopedAt⟩

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open Mettapedia.GSLT.LanguageDef.WellSorted

theorem Admitted.rule_job_focus_open {request : Request} (admitted : Admitted request)
    (representative : Representative request) (job : GeneralRuleJobs.Job)
    (licensed : job.Valid request.plan request.bound request.expected representative.pattern) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment request.plan).language
      request.plan.snapshot.free job.site.focusBound job.site.focusType job.site.focus := by
  apply licensed.2.focus_open
  exact (GeneralPlanEnvironment.typing_iff request.plan request.bound request.expected
    representative.pattern).mpr (admitted.representative_source_typed representative)

theorem equation_job_focus_open {request : Request} {source : Syntax.Pattern}
    (typed : EquationSourceTyped request source) (job : GeneralEquationJobs.Job)
    (licensed : GeneralEquationJobs.LicensedJob request.plan request.bound request.expected source job) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment request.plan).language
      request.plan.snapshot.free job.site.focusBound job.site.focusType job.site.focus := by
  apply licensed.2.focus_open
  exact (GeneralPlanEnvironment.typing_iff request.plan request.bound request.expected source).mpr typed

#print axioms Admitted.rule_job_focus_open
#print axioms equation_job_focus_open

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
