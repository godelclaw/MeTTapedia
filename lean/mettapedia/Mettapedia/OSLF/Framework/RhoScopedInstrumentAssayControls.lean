import Mettapedia.OSLF.Framework.RhoScopedInstrumentAssayReadout
import Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssayControls
import Mettapedia.OSLF.Framework.RhoScopedPartialObserverControls

/-!
# Funded observer readouts on an actual original reflection target

The nine-token original occurrence, delivery and inspection returns an
observer certificate with the exact target and current native origin. Eight
tokens retain the funded reaction and its same target, but return no answer
and eliminate no candidate. The partial structural kit is unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentAssayControls

open Mettapedia.OSLF.Binding RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedInstrumentProperBase RhoScopedInstrumentAdmissionControls
open RhoScopedFundedNativeAssays RhoScopedFundedNativeAssayControls RhoScopedFundedInspection
open RhoScopedInstrumentQuestionTranslation RhoScopedInstrumentAssayReadout
open Mettapedia.GSLT.Causality ComplementaryAssay

theorem paid_original_target_satisfies_observer_question :
    ObserverCertificate withReflection RhoScopedFundedInspectionControls.question Verdict.confirm
      RhoQuotationClassFibres.suspended :=
  (observer_certificate_iff_original withReflection _ _ _).mpr complete_answer_retains_current_certificate

theorem funded_native_source_has_the_actual_proper_reaction :
    (base withReflection).act (source := ([], Srt.pr)) (target := ([], Srt.pr))
      ⟨[], zero []⟩ (Quotient.out native.1)
      (Quotient.out (currentTarget withReflection
        RhoScopedDependentEventFutures.quotedTargetOrigins native)) :=
  native_reaction_is_original_proper withReflection _ native

theorem budget_does_not_change_observer_truth :
    ObserverCertificate withReflection RhoScopedFundedInspectionControls.question Verdict.confirm
      (currentTarget withReflection RhoScopedDependentEventFutures.quotedTargetOrigins native) ∧
    (assay 8 (by decide) (by decide)).responses = 0 := by
  rw [exact_target]
  exact ⟨paid_original_target_satisfies_observer_question, incomplete_price_emits_no_verdict⟩

theorem inadequate_funding_eliminates_no_candidate :
    (assay 8 (by decide) (by decide)).revise predictions {false, true} = {false, true} :=
  short_budget_preserves_candidates

theorem complete_paid_answer_eliminates_the_false_prediction :
    (assay 9 (by decide) (by decide)).revise predictions {false, true} = {true} :=
  complete_answer_revises_candidates

theorem target_question_uses_no_structural_instruments :
    SortedInstrumentCongruence.Formula.Allowed noStructuralInstruments
      (stage RhoScopedFundedInspectionControls.question) :=
  question_needs_no_structural_permission _ _

end Mettapedia.OSLF.Framework.RhoScopedInstrumentAssayControls
