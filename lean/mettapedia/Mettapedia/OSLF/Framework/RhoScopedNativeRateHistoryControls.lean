import Mettapedia.OSLF.Framework.RhoScopedNativeRateHistory
import Mettapedia.OSLF.Framework.RhoScopedDependentEventFutureControls
import Mettapedia.OSLF.Framework.RhoScopeOperationalFutureControls
import Mettapedia.OSLF.Syntax.RhoDropProfile

/-!
# Configured original prices, genuine paid words and nonnatural tariffs

The chosen schedule charges different original rule kinds. Native witnesses
and complete receipt origins are retained independently of affordability.
Configured index rates survive fresh-context transport. A tariff inspecting
an unused original continuation changes under an actual closing substitution,
even though its emitted process is unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedNativeRateHistoryControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedNativeRateHistory RhoScopedDependentEventFutureControls RhoScopedDependentEventFutures
open DisplayedPresheafComprehension PresheafEventCertificates

def rates : SourceRule → Nat
  | .communication => 2
  | .reflection => 5

theorem both_supplied_origins_funded :
    Nonempty (NativePaid withReflection quotedTargetOrigins rates (originCertificate visible rfl) 5) ∧
    Nonempty (NativePaid withReflection quotedTargetOrigins rates
      (originCertificate suspended same_actual_name) 5) := by
  constructor <;> apply (native_paid_iff withReflection quotedTargetOrigins rates _ _).mpr <;>
    exact Nat.le_refl 5

theorem four_units_cannot_pay_for_the_supplied_certificate :
    ¬ Nonempty (NativePaid withReflection quotedTargetOrigins rates
      (originCertificate visible rfl) 4) := by
  intro funding
  exact (by decide : ¬ ((5 : Nat) ≤ 4))
    ((native_paid_iff withReflection quotedTargetOrigins rates _ _).mp funding)

theorem genuine_word_and_complete_target_witness :
    ∃ funding : NativePaid withReflection quotedTargetOrigins rates (originCertificate visible rfl) 5,
      funding.eventWord = [nativeOccurrence withReflection quotedTargetOrigins (originCertificate visible rfl)] ∧
      ((targetReadout withReflection quotedTargetOrigins).app closedWorld
        (originCertificate visible rfl)).2.val = visible := by
  obtain ⟨funding⟩ := both_supplied_origins_funded.1
  exact ⟨funding, native_paid_word withReflection quotedTargetOrigins rates _ 5 funding,
    exact_origin_readout visible rfl⟩

theorem every_distinct_rule_receipt_is_funded (count : Nat) :
    Nonempty (NativePaid withReflection quotedTargetOrigins rates (ruleCertificate count) 5) :=
  (native_paid_iff withReflection quotedTargetOrigins rates _ _).mpr (Nat.le_refl 5)

theorem same_funding_preserves_both_future_origins :
    Nonempty (NativePaid withReflection quotedTargetOrigins rates
      ((totalSpace (certificates withReflection quotedTargetOrigins)).map freshName.val.op
        (originCertificate visible rfl)) 5) ∧
    Nonempty (NativePaid withReflection quotedTargetOrigins rates
      ((totalSpace (certificates withReflection quotedTargetOrigins)).map freshName.val.op
        (originCertificate suspended same_actual_name)) 5) :=
  ⟨(native_funding_preserved_at_future withReflection quotedTargetOrigins rates freshName.val.op _ _).mpr
      both_supplied_origins_funded.1,
    (native_funding_preserved_at_future withReflection quotedTargetOrigins rates freshName.val.op _ _).mpr
      both_supplied_origins_funded.2⟩

def unusedVariableRoot : Root sourceRules withReflection [Srt.pr] :=
  ⟨⟨.reflection, trivial⟩, RhoScopedInstanceReadout.reflection null (.var (.succ .zero))⟩

def closeUnusedVariable : Sub sig [Srt.pr] [] := extend RhoSourceOutputPredicate.output

def bodyTariff {context : Ctx sig} (root : Root sourceRules withReflection context) : Nat :=
  RhoSchema.outputCount (root.2.body 0) + 1

theorem original_body_tariff_changes : bodyTariff unusedVariableRoot = 1 ∧
    bodyTariff (unusedVariableRoot.map closeUnusedVariable) = 2 := by
  constructor <;> rfl

theorem original_body_tariff_is_not_substitution_invariant :
    bodyTariff (unusedVariableRoot.map closeUnusedVariable) ≠ bodyTariff unusedVariableRoot := by
  rw [original_body_tariff_changes.1, original_body_tariff_changes.2]
  decide

theorem target_unchanged_when_unused_tariff_changes :
    (unusedVariableRoot.map closeUnusedVariable).target = zero [] := rfl

end Mettapedia.OSLF.Framework.RhoScopedNativeRateHistoryControls
