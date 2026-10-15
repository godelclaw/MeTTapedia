import Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssays
import Mettapedia.OSLF.Framework.RhoScopedNativeRateHistoryControls
import Mettapedia.OSLF.Framework.RhoScopedFundedInspectionControls

/-!
# Original native event, configured reaction price and completed target assay

An actual reflection event returns the suspended process. Its native family
retains that exact target origin. The supplied budget funds the complete
original occurrence and the delivery and instruction scan that follow it.
One unit below the combined price still funds the reaction and delivery but
does not complete inspection or emit a verdict.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssayControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedDependentEventFutures RhoScopedNativeRateHistory RhoScopedFundedNativeAssays
open DisplayedPresheafComprehension PresheafEventCertificates
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

def suspendedRoot : Root sourceRules withReflection [] :=
  ⟨⟨.reflection, trivial⟩, RhoScopedInstanceReadout.reflection suspendedRaw null⟩

def suspendedEvent : (RhoScopedEventPresheaf.events withReflection).obj
    RhoScopedDependentEventFutureControls.closedWorld := (suspendedRoot, zero [])

theorem supplied_target : join suspendedEvent.1.target suspendedEvent.2 = suspended :=
  join_zero_right suspended

def native : NativeReceipt withReflection quotedTargetOrigins (context := []) :=
  ⟨join suspendedEvent.1.source suspendedEvent.2,
    RhoScopedDependentEventFutures.introduce withReflection quotedTargetOrigins _ suspendedEvent
      ⟨suspended, (congrArg quote supplied_target).symm⟩⟩

theorem exact_target : currentTarget withReflection quotedTargetOrigins native = suspended :=
  supplied_target

theorem exact_native_origin :
    ((targetReadout withReflection quotedTargetOrigins).app AtContext native).2.val = suspended := rfl

theorem configured_reaction_price :
    reactionPrice withReflection quotedTargetOrigins RhoScopedNativeRateHistoryControls.rates native = 5 := rfl

def actual_original_target_reaction :
    RhoScopedParallelReactiveSystem.Firing (rules := sourceRules) (admitted := withReflection)
      native.1 (zero []) (currentTarget withReflection quotedTargetOrigins native) :=
  currentReaction withReflection quotedTargetOrigins native

theorem target_offered : RhoScopedFundedInspectionControls.request.arrival =
    some (currentTarget withReflection quotedTargetOrigins native) := by
  rw [exact_target]
  rfl

def assay (budget : Nat) (reactionAffordable : 5 ≤ budget)
    (deliveryAffordable : 1 ≤ budget - 5) :=
  Receipt.inspect (admitted := withReflection) (family := quotedTargetOrigins)
    (rates := RhoScopedNativeRateHistoryControls.rates) (native := native)
    (deliveryCost := RhoScopedFundedInspectionControls.deliveryRate)
    (request := RhoScopedFundedInspectionControls.request) (budget := budget)
    (by rw [configured_reaction_price]; exact reactionAffordable) target_offered
    (by change 1 ≤ budget - _; rw [configured_reaction_price]; exact deliveryAffordable)

theorem complete_price_emits_target_certificate :
    (assay 9 (by decide) (by decide)).responses = {(21, Verdict.confirm, 12, suspended)} := by
  rw [assay, Receipt.inspect_responses, exact_target, configured_reaction_price]
  change (if 5 + 1 + (RhoScopedFundedInspection.protocol withReflection []
      RhoScopedFundedInspectionControls.deliveryRate).inspectionCost
      RhoScopedFundedInspectionControls.question suspended ≤ 9 then
    {(21, verdictOf ((RhoScopedFundedInspection.protocol withReflection []
      RhoScopedFundedInspectionControls.deliveryRate).test
      RhoScopedFundedInspectionControls.question suspended), 12, suspended)} else 0) = _
  rw [RhoScopedFundedInspectionControls.actual_two_outcome_inspection_price,
    RhoScopedFundedInspectionControls.actual_two_outcome_guard_confirms]
  rfl

theorem incomplete_price_emits_no_verdict :
    (assay 8 (by decide) (by decide)).responses = 0 := by
  rw [assay, Receipt.inspect_responses, exact_target, configured_reaction_price]
  change (if 5 + 1 + (RhoScopedFundedInspection.protocol withReflection []
      RhoScopedFundedInspectionControls.deliveryRate).inspectionCost
      RhoScopedFundedInspectionControls.question suspended ≤ 8 then _ else 0) = 0
  rw [RhoScopedFundedInspectionControls.actual_two_outcome_inspection_price]
  rfl

theorem short_budget_still_retains_funded_reaction :
    (assay 8 (by decide) (by decide)).funding.eventWord =
      [nativeOccurrence withReflection quotedTargetOrigins native] :=
  native_paid_word withReflection quotedTargetOrigins RhoScopedNativeRateHistoryControls.rates
    native 8 (assay 8 (by decide) (by decide)).funding

theorem complete_answer_retains_current_certificate :
    RhoScopedFundedInspection.StageCertificate withReflection
      RhoScopedFundedInspectionControls.question Verdict.confirm suspended := by
  have reported : (21, Verdict.confirm, 12, suspended) ∈
      (assay 9 (by decide) (by decide)).responses := by
    rw [complete_price_emits_target_certificate]
    exact Multiset.mem_singleton_self _
  obtain ⟨answer, _arrival, readout, certificate, _spent⟩ :=
    Receipt.current_target_certificate (assay 9 (by decide) (by decide)) _ reported
  have verdict : Verdict.confirm = verdictOf answer := congrArg (fun response => response.2.1) readout
  rw [← verdict, exact_target] at certificate
  exact certificate

theorem complete_answer_price_and_balance :
    (assay 9 (by decide) (by decide)).spent = 9 ∧
      (assay 9 (by decide) (by decide)).remaining = 0 := by
  have reported : (21, Verdict.confirm, 12, suspended) ∈
      (assay 9 (by decide) (by decide)).responses := by
    rw [complete_price_emits_target_certificate]
    exact Multiset.mem_singleton_self _
  obtain ⟨_answer, _arrival, _readout, _certificate, spent⟩ :=
    Receipt.current_target_certificate (assay 9 (by decide) (by decide)) _ reported
  rw [configured_reaction_price, exact_target] at spent
  change (assay 9 (by decide) (by decide)).spent =
    5 + 1 + (RhoScopedFundedInspection.protocol withReflection []
      RhoScopedFundedInspectionControls.deliveryRate).inspectionCost
      RhoScopedFundedInspectionControls.question suspended at spent
  rw [RhoScopedFundedInspectionControls.actual_two_outcome_inspection_price] at spent
  have ledger := Receipt.complete_ledger (assay 9 (by decide) (by decide))
  constructor
  · exact spent
  · omega

def predictions (hypothesis : Bool) (_question : RhoScopedFundedInspection.Question []) : Bool := hypothesis

theorem complete_answer_revises_candidates :
    (assay 9 (by decide) (by decide)).revise predictions {false, true} = {true} := by
  unfold Receipt.revise
  rw [complete_price_emits_target_certificate]
  ext hypothesis
  cases hypothesis <;>
    simp [FiniteAssayLearner.revise, FiniteAssayLearner.Compatible, predictions,
      ComplementaryAssay.Verdict.bit]

theorem short_budget_preserves_candidates :
    (assay 8 (by decide) (by decide)).revise predictions {false, true} = {false, true} :=
  Receipt.silence_preserves_candidates _ _ _ incomplete_price_emits_no_verdict

end Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssayControls
