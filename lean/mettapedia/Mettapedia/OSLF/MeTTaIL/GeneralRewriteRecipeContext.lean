import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceLocalReplacement
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs

/-!
# Context transport of original authored rewrite receipts

Concrete typed sites compose through the existing one-hole context algebra.
The selected declaration frames and physical addresses concatenate, while
the inner focus, exact binder context and type remain literal data.

Original rule and equation receipts transport through independently licensed
outer occurrences, preserving their matching, assignments, premise histories
and local results. Source and local admission plus the actual representation
checks earn whole-target admission. Equation transport also earns the exact
metadata-erasure endpoint. The original completion implementations emit the
constructed receipts.

The local environment and carrier must already match the outer focus. This
is not implicit rebasing of an ambient assignment, transport across a changed
provider snapshot, or an assertion that arbitrary effects commute.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Syntax DerivedContexts

/-- Compose the two original typed occurrence records. Physical path and
selected typing-declaration frames concatenate; the inner local carrier is
retained literally. -/
def SiteData.compose (outer inner : SiteData) : SiteData where
  address := outer.address ++ inner.address
  context := outer.context.comp inner.context
  focus := inner.focus
  focusBound := inner.focusBound
  focusType := inner.focusType
  typingFrames := outer.typingFrames ++ inner.typingFrames

@[simp] theorem SiteData.compose_fill (outer inner : SiteData) (target : Pattern) :
    (outer.compose inner).context.fill target = outer.context.fill (inner.context.fill target) :=
  OneHoleContext.fill_comp _ _ _

end Mettapedia.OSLF.MeTTaIL.GeneralTypedSites

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- An independently licensed inner site transports through the actual outer
source typing descent, retaining both chosen declaration paths. -/
theorem compose {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {outer inner : SiteData}
    (outside : Licensed language free permissions bound expected source outer)
    (inside : Licensed language free permissions outer.focusBound outer.focusType outer.focus inner) :
    Licensed language free permissions bound expected source (outer.compose inner) := by
  induction outside with
  | here _ _ _ => exact inside
  | application declared ordinary arguments objects selected parameterSelected parameterTyped permitted _ ih =>
      exact .application declared ordinary arguments objects selected parameterSelected parameterTyped permitted (ih inside)
  | lambda permitted _ ih => exact .lambda permitted (ih inside)
  | multiLambda permitted _ ih => exact .multiLambda permitted (ih inside)
  | directCollection permitted elements objects selected _ ih =>
      exact .directCollection permitted elements objects selected (ih inside)
  | authoredCollection declared shape permitted elements objects selected _ ih =>
      exact .authoredCollection declared shape permitted elements objects selected (ih inside)

/-- The actual outer parameter representations and actual inner checks
compose; no global abstraction-shape equivalence is assumed. -/
theorem acceptsReplacement_compose {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {outer : SiteData}
    (outside : Licensed language free permissions bound expected source outer)
    (inner : SiteData) (target : Pattern)
    (outerRepresented : outer.acceptsReplacementRepresentation language (inner.context.fill target) = true)
    (innerRepresented : inner.acceptsReplacementRepresentation language target = true) :
    (outer.compose inner).acceptsReplacementRepresentation language target = true := by
  induction outside with
  | here _ _ _ => exact innerRepresented
  | @application bound rule declaration index arguments argument parameter parameterType site
      declared ordinary argumentsTyped objects selected parameterSelected parameterTyped permitted _ ih =>
      have declarationAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
      simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapApplication,
        replacementRepresentations?, declarationAt, Option.bind_some, parameterSelected,
        Bool.and_eq_true] at outerRepresented
      simp only [SiteData.acceptsReplacementRepresentation, SiteData.compose, SiteData.wrapApplication,
        OneHoleContext.comp, List.cons_append, replacementRepresentations?, declarationAt,
        Option.bind_some, parameterSelected, Bool.and_eq_true, OneHoleContext.fill_comp]
      exact ⟨outerRepresented.1, ih outerRepresented.2⟩
  | lambda _ _ ih => exact ih outerRepresented
  | multiLambda _ _ ih => exact ih outerRepresented
  | directCollection _ _ _ _ _ ih => exact ih outerRepresented
  | authoredCollection _ _ _ _ _ _ _ ih => exact ih outerRepresented

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission GeneralTypedSites DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-- Reuse an original finite local receipt inside a typed enclosing site.
Its declaration and all local firing evidence remain literal original data. -/
def Receipt.inContext (receipt : Receipt) (outside : SiteData) : Receipt :=
  {receipt with
    job := {receipt.job with site := outside.compose receipt.job.site}
    target := outside.context.fill receipt.target}

/-- Context transport reuses the same local environment and binder context.
It earns the enclosing source and target judgments from the independently
licensed outer occurrence, rather than assuming a valid lifted receipt. -/
theorem Receipt.inContext_validWith {dynamic : GeneralPremise.DynamicProvider} {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {outside : SiteData}
    {receipt : Receipt}
    (licensed : Licensed (GeneralPlanEnvironment.environmentWith plan dynamic).language plan.snapshot.free
      plan.permissions.sites bound expected source outside)
    (sourceAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environmentWith plan dynamic).language
      plan.snapshot.free bound expected source)
    (localValid : receipt.ValidWith dynamic plan outside.focusBound outside.focusType outside.focus)
    (represented : outside.acceptsReplacementRepresentation (GeneralPlanEnvironment.environmentWith plan dynamic).language
      receipt.target = true) :
    (receipt.inContext outside).ValidWith dynamic plan bound expected source := by
  have innerLicensed := licensed.compose localValid.1.2
  have globalTarget := licensed.replace_locally_openPatternWellSorted sourceAdmitted
    receipt.target represented localValid.2.2.2.2
  have outerRepresented : outside.acceptsReplacementRepresentation
      (GeneralPlanEnvironment.environmentWith plan dynamic).language
      (receipt.job.site.context.fill receipt.localTarget) = true := by
    rw [← localValid.2.2.2.1]
    exact represented
  have combinedRepresented := licensed.acceptsReplacement_compose receipt.job.site receipt.localTarget
    outerRepresented localValid.2.2.1
  refine ⟨⟨localValid.1.1,innerLicensed⟩,localValid.2.1,combinedRepresented,?_,globalTarget⟩
  change outside.context.fill receipt.target = (outside.compose receipt.job.site).context.fill receipt.localTarget
  rw [SiteData.compose_fill, localValid.2.2.2.1]

/-- The existing actual receipt constructor accepts the transported evidence.
No repeated matcher or premise search is needed to construct this witness. -/
theorem Receipt.finishWith_inContext {dynamic : GeneralPremise.DynamicProvider} {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {outside : SiteData}
    {receipt : Receipt}
    (licensed : Licensed (GeneralPlanEnvironment.environmentWith plan dynamic).language plan.snapshot.free
      plan.permissions.sites bound expected source outside)
    (sourceAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environmentWith plan dynamic).language
      plan.snapshot.free bound expected source)
    (localValid : receipt.ValidWith dynamic plan outside.focusBound outside.focusType outside.focus)
    (represented : outside.acceptsReplacementRepresentation (GeneralPlanEnvironment.environmentWith plan dynamic).language
      receipt.target = true) :
    finishWith? dynamic plan bound expected (receipt.inContext outside).job
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory =
        some (receipt.inContext outside) :=
  finishWith_complete (receipt.inContext_validWith licensed sourceAdmitted localValid represented)

@[simp] theorem Receipt.inContext_here (receipt : Receipt) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    receipt.inContext (SiteData.here bound expected source) = receipt := by
  cases receipt
  rfl

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

namespace Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Syntax DerivedContexts

theorem SiteData.compose_assoc (outside middle inside : SiteData) :
    (outside.compose middle).compose inside = outside.compose (middle.compose inside) := by
  simp only [SiteData.compose, List.append_assoc, OneHoleContext.comp_assoc]

end Mettapedia.OSLF.MeTTaIL.GeneralTypedSites

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
open GeneralTypedSites DerivedContexts

/-- Repeated enclosure is exactly the existing zipper composition, including
literal local proof fields and original physical/declaration addresses. -/
theorem Receipt.inContext_comp (receipt : Receipt) (outside middle : SiteData) :
    (receipt.inContext middle).inContext outside = receipt.inContext (outside.compose middle) := by
  simp only [Receipt.inContext, SiteData.compose_assoc, SiteData.compose_fill]

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission GeneralTypedSites DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-- Enclose an existing original equation receipt without changing its local
matching, ordered premises, source declaration or raw reduct. -/
def Receipt.inContext (receipt : Receipt) (outside : SiteData) : Receipt :=
  {receipt with
    job := {receipt.job with site := outside.compose receipt.job.site}
    target := outside.context.fill receipt.target}

/-- For an admitted original source, the local raw canonical reduct already
fills to a canonical object. The endpoint's metadata erasure is therefore
literal identity at this specific independently licensed occurrence. -/
theorem Completion.endpoint_without_erasure {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {receipt : Receipt}
    (valid : Completion plan bound expected source receipt) :
    receipt.target = receipt.job.site.context.fill receipt.rawReduct.eraseBinderMetadata := by
  have admitted := valid.job.2.replace_locally_openPatternWellSorted valid.sourceTyped
    receipt.rawReduct.eraseBinderMetadata valid.accepted.1 valid.accepted.2.1
  rw [valid.endpoint, Pattern.eraseBinderMetadata_eq_self_of_canonical admitted.2.1]

/-- Original equation completion transports through an independently licensed
outer source, with its actual representation check. Local binder contexts and
all premise/provider evidence remain unchanged. -/
theorem Receipt.inContext_completion {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {outside : SiteData}
    {receipt : Receipt}
    (licensed : Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound expected source outside)
    (sourceAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound expected source)
    (localValid : Completion plan outside.focusBound outside.focusType outside.focus receipt)
    (represented : outside.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language
      receipt.target = true) :
    Completion plan bound expected source (receipt.inContext outside) := by
  have combinedLicensed := licensed.compose localValid.job.2
  have localTarget : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free outside.focusBound outside.focusType receipt.target := by
    rw [localValid.endpoint]
    exact localValid.accepted.2.2
  have globalTarget := licensed.replace_locally_openPatternWellSorted sourceAdmitted
    receipt.target represented localTarget
  have innerEndpoint := localValid.endpoint_without_erasure
  have outerRepresented : outside.acceptsReplacementRepresentation
      (GeneralPlanEnvironment.environment plan).language
      (receipt.job.site.context.fill receipt.rawReduct.eraseBinderMetadata) = true := by
    rw [← innerEndpoint]
    exact represented
  have combinedRepresented := licensed.acceptsReplacement_compose receipt.job.site
    receipt.rawReduct.eraseBinderMetadata outerRepresented localValid.accepted.1
  have endpoint : outside.context.fill receipt.target =
      ((outside.compose receipt.job.site).context.fill receipt.rawReduct.eraseBinderMetadata).eraseBinderMetadata := by
    rw [SiteData.compose_fill, ← innerEndpoint,
      Pattern.eraseBinderMetadata_eq_self_of_canonical globalTarget.2.1]
  refine ⟨⟨localValid.job.1,combinedLicensed⟩,sourceAdmitted,
    localValid.matched,localValid.capturedTyped,localValid.premises,localValid.completedTyped,
    localValid.reduct,⟨combinedRepresented,localValid.accepted.2.1,?_⟩,endpoint⟩
  change OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
    bound expected ((outside.compose receipt.job.site).context.fill receipt.rawReduct.eraseBinderMetadata).eraseBinderMetadata
  rw [← endpoint]
  exact globalTarget

/-- The original completion implementation emits the exact transported data. -/
theorem Receipt.finish_inContext {plan : Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {outside : SiteData}
    {receipt : Receipt}
    (licensed : Licensed (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      plan.permissions.sites bound expected source outside)
    (sourceAdmitted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound expected source)
    (localValid : Completion plan outside.focusBound outside.focusType outside.focus receipt)
    (represented : outside.acceptsReplacementRepresentation (GeneralPlanEnvironment.environment plan).language
      receipt.target = true) :
    finish plan bound expected (receipt.inContext outside).job
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory =
        some (receipt.inContext outside) :=
  finish_complete (receipt.inContext_completion licensed sourceAdmitted localValid represented)

@[simp] theorem Receipt.inContext_here (receipt : Receipt) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    receipt.inContext (SiteData.here bound expected source) = receipt := by
  cases receipt
  rfl

theorem Receipt.inContext_comp (receipt : Receipt) (outside middle : SiteData) :
    (receipt.inContext middle).inContext outside = receipt.inContext (outside.compose middle) := by
  simp only [Receipt.inContext, SiteData.compose_assoc, SiteData.compose_fill]

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
