import Mettapedia.OSLF.Syntax.ScopedBindingEquationFundedPossibility
import Mettapedia.OSLF.Syntax.RhoScopedEquationNativeControls

/-!
# Actual rho occurrences with separate native and financial admission

Two authored occurrences emit the same process and admit the same dependent
certificate value. A nonconstant declared price funds one and rejects the
other at budget one. Their retained origins therefore matter financially.

The source binding profile remains explicit. Closing a caller under an
input preserves funding for an already permitted occurrence; budget does
not turn a forbidden reaction position into a permitted one.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationFundingControls

open RhoSchema ScopedEncoding ScopedEquationEvents
open RhoScopedEquationEventControls RhoScopedEquationBindingControls RhoScopedEquationNativeControls
open ScopedEquationNativePossibility ScopedEquationFundedPossibility

def profile (index : Fin 2) : Nat := index.val + 1

abbrev emissionFunding (index value : Fin 2) (amount : Nat) :=
  Funding outputCertificates (emitReceipt index value) profile amount

theorem emission_funding_iff (index value : Fin 2) (amount : Nat) :
    Nonempty (emissionFunding index value amount) ↔ index.val + 1 ≤ amount :=
  funding_iff outputCertificates (emitReceipt index value) profile amount

theorem actual_emission_with_full_certificate :
    ∃ funding : emissionFunding 0 1 1,
      funding.eventWord = [emitOccurrence 0] ∧
        (receiptCertificate outputCertificates (emitReceipt 0 1)).val = 1 := by
  obtain ⟨funding⟩ := (emission_funding_iff 0 1 1).mpr (by decide)
  exact ⟨funding, funded_word_retains_event outputCertificates (emitReceipt 0 1) profile 1 funding,
    native_receipt_keeps_certificate 0 1⟩

theorem same_endpoints_and_certificate_different_funding :
    (emitOccurrence 0).sourceClass rhoSourceE = (emitOccurrence 1).sourceClass rhoSourceE ∧
      (emitOccurrence 0).targetClass rhoSourceE = (emitOccurrence 1).targetClass rhoSourceE ∧
      (receiptCertificate outputCertificates (emitReceipt 0 1)).val =
        (receiptCertificate outputCertificates (emitReceipt 1 1)).val ∧
      Nonempty (emissionFunding 0 1 1) ∧ ¬ Nonempty (emissionFunding 1 1 1) := by
  refine ⟨rfl, rfl, rfl, (emission_funding_iff 0 1 1).mpr (by decide), ?_⟩
  intro funding
  have unaffordable := (emission_funding_iff 1 1 1).mp funding
  exact (by decide : ¬ ((1 : Fin 2).val + 1 ≤ 1)) unaffordable

theorem empty_budget_does_not_pay_for_a_native_certificate :
    ¬ Nonempty (emissionFunding 0 1 0) := by
  intro funding
  have unaffordable := (emission_funding_iff 0 1 0).mp funding
  exact (by decide : ¬ ((0 : Fin 2).val + 1 ≤ 0)) unaffordable

theorem two_units_admit_both_origins :
    Nonempty (emissionFunding 0 1 2) ∧ Nonempty (emissionFunding 1 1 2) :=
  ⟨(emission_funding_iff 0 1 2).mpr (by decide),
    (emission_funding_iff 1 1 2).mpr (by decide)⟩

theorem actual_binding_substitution_preserves_funding :
    ScopedEquationResources.AffordableHistory rhoSourceE rules allPositions ([], Srt.pr)
      profile (underInput.map [] closeCaller) 1 ↔
        ScopedEquationResources.AffordableHistory rhoSourceE rules allPositions ([Srt.nm], Srt.pr)
          profile underInput 1 :=
  ScopedEquationResources.substitution_preserves_affordability rhoSourceE rules allPositions
    ([Srt.nm], Srt.pr) profile underInput [] closeCaller 1

theorem actual_open_binding_history_funded :
    Nonempty (ScopedEquationResources.PaidHistory rhoSourceE rules allPositions ([Srt.nm], Srt.pr)
      profile underInput 1) :=
  (ScopedEquationResources.paid_history_nonempty_iff rhoSourceE rules allPositions ([Srt.nm], Srt.pr)
    profile underInput 1).mpr (by decide)

theorem actual_closed_binding_history_funded :
    Nonempty (ScopedEquationResources.PaidHistory rhoSourceE rules allPositions ([], Srt.pr)
      profile (underInput.map [] closeCaller) 1) :=
  (ScopedEquationResources.paid_history_nonempty_iff rhoSourceE rules allPositions ([], Srt.pr)
    profile (underInput.map [] closeCaller) 1).mpr (by decide)

theorem funding_cannot_admit_the_inactive_parallel_position (amount : Nat) :
    ¬ ∃ event : Event rules parallelPermission ([Srt.nm], Srt.pr),
      event.holeContext = [Srt.nm, Srt.nm] ∧ HEq event.context underInput.context ∧
        ScopedEquationResources.AffordableHistory rhoSourceE rules parallelPermission
          ([Srt.nm], Srt.pr) profile event amount := by
  rintro ⟨event, sameHole, samePath, _⟩
  exact no_parallel_event_at_this_path ⟨event, sameHole, samePath⟩

end Mettapedia.OSLF.Binding.RhoScopedEquationFundingControls
