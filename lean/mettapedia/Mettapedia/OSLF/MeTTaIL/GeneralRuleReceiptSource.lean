import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

/-!
# Source typing recovered from complete primitive receipts

Licensed typing and objecthood, local canonical source metadata, and the
canonical checked target together recover the complete caller judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleReceiptSource

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Changing a canonical filler cannot introduce binder display metadata. -/
theorem canonical_fill_replace (context : OneHoleContext) {source target : Pattern}
    (outer : (context.fill target).hasCanonicalBinderMetadata = true)
    (inner : source.hasCanonicalBinderMetadata = true) :
    (context.fill source).hasCanonicalBinderMetadata = true := by
  induction context with
  | hole => exact inner
  | apply label before context after ih =>
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      have old := (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp outer
      intro item member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with left | same | right
      · exact old item (List.mem_append_left _ left)
      · subst item
        exact ih (old _ (List.mem_append_right _ (List.mem_cons_self)))
      · exact old item (List.mem_append_right _ (List.mem_cons_of_mem _ right))
  | lambda display context ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at outer ⊢
      exact ⟨outer.1, ih outer.2⟩
  | multiLambda arity display context ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at outer ⊢
      exact ⟨outer.1, ih outer.2⟩
  | substBody context replacement ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at outer ⊢
      exact ⟨ih outer.1, outer.2⟩
  | substReplacement body context ih =>
      simp only [OneHoleContext.fill, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at outer ⊢
      exact ⟨outer.1, ih outer.2⟩
  | collection kind before context after rest ih =>
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      have old := (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp outer
      intro item member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with left | same | right
      · exact old item (List.mem_append_left _ left)
      · subst item
        exact ih (old _ (List.mem_append_right _ (List.mem_cons_self)))
      · exact old item (List.mem_append_right _ (List.mem_cons_of_mem _ right))

/-- A complete primitive receipt types its source, even though the receipt
interface only records source typing at the selected focus explicitly. -/
theorem primitive_source_sorted {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound expected source := by
  have typed := fired.1.2.source_typed
  have object := fired.1.2.source_object
  have localSorted := (GeneralRuleJobs.receipt_root_readout fired).2.1
  have canonical : source.hasCanonicalBinderMetadata = true := by
    rw [← fired.1.2.source_eq]
    apply canonical_fill_replace receipt.job.site.context
      (target := receipt.localTarget) _ localSorted.2.1
    rw [← fired.2.2.2.1]
    exact fired.2.2.2.2.2.1
  exact ⟨typed, canonical, object, typed.isWellScopedAt⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRuleReceiptSource
