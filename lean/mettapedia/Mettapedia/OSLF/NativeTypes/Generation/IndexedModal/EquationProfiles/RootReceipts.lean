import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Receipts
import Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

/-!
# Exact root occurrence receipts and native payloads

The execution ordinal selects the environment's annotated declaration; the
authored declaration index remains separate in the occurrence job. A root
receipt carries the same local and enclosing result. These facts let the
generic occurrence judgment and the native root firing judgment share exact
payloads, including captures and ordered premise evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.RootReceipts

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Use the selected execution ordinal, not the authored declaration index.
For a root occurrence the native result is the local result. -/
def payload (receipt : GeneralRuleJobs.Receipt) : Payload :=
  ⟨receipt.job.ordinal, receipt.matcherTrace, receipt.captured, receipt.completed,
    receipt.premiseHistory, receipt.localTarget⟩

def pack (declaration : RulePlan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (value : Payload) : GeneralRuleJobs.Receipt :=
  ⟨⟨value.index, declaration, SiteData.here bound expected source⟩, value.trace,
    value.captured, value.completed, value.history, value.target, value.target⟩

@[simp] theorem payload_pack (declaration : RulePlan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (value : Payload) : payload (pack declaration bound expected source value) = value := by
  cases value
  rfl

/-- No site, type or ambient-context weakening occurs in root extraction. -/
theorem payload_valid {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source)
    (root : receipt.job.site = SiteData.here bound expected source) :
    Valid (GeneralPlanEnvironment.environment plan) bound expected source (payload receipt) := by
  have fires := valid.2.1
  rw [root] at fires
  exact fires

theorem target_eq_local {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source)
    (root : receipt.job.site = SiteData.here bound expected source) :
    receipt.target = receipt.localTarget := by
  simpa only [root, SiteData.here, DerivedContexts.OneHoleContext.fill] using valid.2.2.2.1

/-- An independently specified native firing constructs an actual licensed
occurrence at the root, retaining both the selected and authored ordinals. -/
theorem pack_valid {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {value : Payload} {declaration : RulePlan}
    (declared : (declaration, value.index) ∈ plan.rules.zipIdx)
    (enabled : plan.permissions.sites.enabled = true)
    (fires : Valid (GeneralPlanEnvironment.environment plan) bound expected source value) :
    (pack declaration bound expected source value).Valid plan bound expected source := by
  have typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free bound expected source ∧
      OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        plan.snapshot.free bound expected value.target := by
    cases fires with
    | fire _ _ _ sourceTyped _ _ _ _ targetTyped => exact ⟨sourceTyped, targetTyped⟩
  refine ⟨⟨declared, .here enabled typed.1.2.2.1 typed.1.1⟩, fires, ?_, rfl, typed.2⟩
  rfl

theorem pack_valid_iff {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {value : Payload} {declaration : RulePlan}
    (declared : (declaration, value.index) ∈ plan.rules.zipIdx)
    (enabled : plan.permissions.sites.enabled = true) :
    (pack declaration bound expected source value).Valid plan bound expected source ↔
      Valid (GeneralPlanEnvironment.environment plan) bound expected source value := by
  constructor
  · intro valid
    simpa only [payload_pack] using payload_valid valid rfl
  · exact pack_valid declared enabled

/-- Packing an actual root receipt recovers that entire receipt, not only
its target or a selected declaration's name. -/
theorem pack_payload {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source)
    (root : receipt.job.site = SiteData.here bound expected source) :
    pack receipt.job.declaration bound expected source (payload receipt) = receipt := by
  have same := target_eq_local valid root
  cases receipt with
  | mk job trace captured completed history localTarget target =>
    cases job with
    | mk ordinal declaration site =>
      change site = SiteData.here bound expected source at root
      cases root
      cases same
      rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.RootReceipts
