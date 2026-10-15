import Mettapedia.OSLF.Syntax.ScopedBindingEventPrices
import Mettapedia.OSLF.Syntax.RhoScopedEquationNativeControls

/-!
# A native certificate can survive a substitution that raises its price

The actual open COMM returns the caller's process variable. Replacing that
variable by an output transports the native certificate but increases an
equation-invariant target-sensitive price from one to two. Budget one admits
the original event and rejects the mapped one; budget two admits both.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEventPriceControls

open ScopedEquationEvents ScopedEncoding
open RhoSchema RhoScopedEquationEventControls RhoScopedEquationNativeControls
open ScopedBindingEventPrices

noncomputable section

def targetPrice {scope : Scope sig} (event : Event rules parallelPermission scope) : Nat :=
  RhoSourceOutputPredicate.count (event.targetClass rhoSourceE) + 1

theorem original_price_one : targetPrice openProcessOccurrence = 1 := by
  change outputCount openProcessOccurrence.target + 1 = 1
  rw [actual_open_process_target]
  rfl

theorem future_price_two : targetPrice (openProcessOccurrence.map [] supplyOutput) = 2 := by
  change outputCount (openProcessOccurrence.map [] supplyOutput).target + 1 = 2
  rw [actual_future_process_target]
  rfl

theorem original_event_has_actual_unit_funding :
    Nonempty (Funding rhoSourceE rules parallelPermission ([Srt.pr], Srt.pr)
      targetPrice openProcessOccurrence 1) := by
  apply (funding_iff rhoSourceE rules parallelPermission _ targetPrice openProcessOccurrence 1).mpr
  rw [original_price_one]

theorem mapped_event_rejects_unit_funding :
    ¬ Nonempty (Funding rhoSourceE rules parallelPermission ([], Srt.pr)
      targetPrice (openProcessOccurrence.map [] supplyOutput) 1) := by
  intro funded
  have affordable := (funding_iff rhoSourceE rules parallelPermission _ targetPrice _ 1).mp funded
  rw [future_price_two] at affordable
  omega

theorem mapped_event_has_actual_two_unit_funding :
    Nonempty (Funding rhoSourceE rules parallelPermission ([], Srt.pr)
      targetPrice (openProcessOccurrence.map [] supplyOutput) 2) := by
  apply (funding_iff rhoSourceE rules parallelPermission _ targetPrice _ 2).mpr
  rw [future_price_two]

theorem certificate_transport_does_not_transport_the_unit_purse :
    ((ScopedEquationNativePossibility.certified rhoSourceE rules parallelPermission Srt.pr outputCertificates).map
      processChange openProcessCertificate).val = 0 ∧
    Nonempty (Funding rhoSourceE rules parallelPermission ([Srt.pr], Srt.pr)
      targetPrice openProcessOccurrence 1) ∧
    ¬ Nonempty (Funding rhoSourceE rules parallelPermission ([], Srt.pr)
      targetPrice (openProcessOccurrence.map [] supplyOutput) 1) :=
  ⟨future_certificate_action_computes, original_event_has_actual_unit_funding,
    mapped_event_rejects_unit_funding⟩

theorem not_all_budget_agreement_under_actual_substitution :
    ¬ ∀ amount, Nonempty (Funding rhoSourceE rules parallelPermission ([], Srt.pr)
      targetPrice (openProcessOccurrence.map [] supplyOutput) amount) ↔
        Nonempty (Funding rhoSourceE rules parallelPermission ([Srt.pr], Srt.pr)
          targetPrice openProcessOccurrence amount) := by
  intro compares
  have prices := (substitution_funding_iff_price rhoSourceE rules parallelPermission ([Srt.pr], Srt.pr)
    targetPrice [] targetPrice supplyOutput openProcessOccurrence).mp compares
  rw [future_price_two, original_price_one] at prices
  omega

end

end Mettapedia.OSLF.Binding.RhoScopedEventPriceControls
