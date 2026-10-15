import Mettapedia.OSLF.Framework.RhoQuotationAccessControls
import Mettapedia.OSLF.Framework.RhoScopeWhereNativeControls

/-!
# Quotation access at actual guarded rho receptions

The captured closed payload decodes to its supplied source equation class.
The bound continuation returns its dereferenced quotation, which decodes
independently to drop-after-quote. These processes quote to the same name.
Compatible dependent consumers and native predicates therefore agree on
them; their exact process origins need not agree.

The confirming interpreter execution supplies a concrete retained reception.
These semantic readbacks do not execute a native predicate checker or
identify process suspension with a static process beta equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoOperationalQuotationAccess

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback BindingConstructorPredicates
open RhoQuotationDependentAccess RhoQuotationAccessControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereExecutionControls

universe u

def returnedPayload (payload : Term sig [] Srt.pr) : Pattern :=
  .apply "PDrop" [.apply "NQuote" [encodeTerm payload]]

theorem received_readback (payload : Term sig [] Srt.pr) :
    readProcessClass [] (encodeTerm payload) = some (project payload) := by
  obtain ⟨decoded, reading, represented⟩ := read_encoded_class payload
  change readProcess [] (encodeTerm payload) = some decoded at reading
  simp only [readProcessClass, reading, Option.map_some, represented]

theorem returned_readback (payload : Term sig [] Srt.pr) :
    readProcessClass [] (returnedPayload payload) = some (drop (quote (project payload))) := by
  rw [returnedPayload, readProcessClass_drop, readNameClass_quote, received_readback]
  rfl

theorem return_preserves_native_predicate (predicate : Predicate model Srt.pr)
    (compatible : PredicateCompatible predicate) (payload : Term sig [] Srt.pr) :
    predicate.holds (drop (quote (project payload))) ↔ predicate.holds (project payload) :=
  compatible _ _ (quote_drop _)

theorem return_preserves_dependent_consumer (family : Name [] → Type u)
    (consumer : (process : Process []) → family (quote process))
    (compatible : Compatible family consumer) (payload : Term sig [] Srt.pr) :
    HEq (consumer (drop (quote (project payload)))) (consumer (project payload)) :=
  compatible _ _ (quote_drop _)

def receivedReceipt (payload : Term sig [] Srt.pr) :
    QuotationReceipt (top model Srt.pr) (quote (project payload)) :=
  receiptOf _ (project payload) (by trivial)

def returnedReceipt (payload : Term sig [] Srt.pr) :
    QuotationReceipt (top model Srt.pr) (quote (project payload)) where
  arguments := .cons (drop (quote (project payload))) .nil
  admitted := ⟨by trivial, by trivial⟩
  output := (RhoGeneratedScopeSubstitution.quote_operation _).symm.trans (quote_drop _)

theorem return_changes_actual_output_origin :
    receivedReceipt RhoSourceOutputPredicate.output ≠ returnedReceipt RhoSourceOutputPredicate.output := by
  intro same
  have origins := congrArg QuotationReceipt.origin same
  exact suspended_not_visible origins.symm

theorem exact_output_predicate_not_preserved :
    (singletonOrigin visible).holds (project RhoSourceOutputPredicate.output) ∧
      ¬ (singletonOrigin visible).holds (drop (quote (project RhoSourceOutputPredicate.output))) :=
  ⟨supplied_visible_admitted, supplied_suspension_rejected⟩

theorem confirmed_target_readback :
    (firing .confirm .confirm).target =
      .collection .hashBag
        [.apply "POutput" [answerChannel .confirm, returnedPayload (rawPayload .confirm)],
         probe .refute] none ∧
    readProcessClass [] (returnedPayload (rawPayload .confirm)) =
      some (drop (quote (project (rawPayload .confirm)))) ∧
    HEq (inventoryConsumer (drop (quote (project (rawPayload .confirm)))))
      (inventoryConsumer (project (rawPayload .confirm))) :=
  ⟨rfl, returned_readback _, return_preserves_dependent_consumer _ _ inventory_compatible _⟩

theorem confirming_reception_retains_origin :
    (RhoScopeWhereNativeControls.receipt .confirm).origin.val =
      quote (project (rawPayload .confirm)) ∧
    QuotationReceipt.origin (receivedReceipt (rawPayload .confirm)) = project (rawPayload .confirm) :=
  ⟨rfl, rfl⟩

end Mettapedia.OSLF.Framework.RhoOperationalQuotationAccess
