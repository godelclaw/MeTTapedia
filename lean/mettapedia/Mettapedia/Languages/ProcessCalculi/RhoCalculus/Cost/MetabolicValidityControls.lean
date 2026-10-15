import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicFundingExecution

/-!
# Source funding validity is stronger than executable rho data

A structurally present cell can carry the empty signature. The raw protocol
can communicate this data, but it does not earn any signing-atom expenditure.
Source runtime admission rejects that cell. Thus structural cell counts become
token prices only under the declared unit-cell or signature-valuation contract.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.ValidityControls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical LanguageDefGSLT ResourcePredation
open StackInternalization FundingExecution

def emptySignatureCell : CostStack Nat := .cons 0 .empty

def actualReceipt := executePrefix emptySignatureCell .empty []

theorem actual_communications : actualReceipt.execution.length = 2 := by
  rw [actualReceipt, prefix_administrative_count]
  rfl

theorem actual_public_path :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step
      (readout (prefixInitial emptySignatureCell .empty [])) (readout actualReceipt.target) :=
  prefix_actual_public_path emptySignatureCell .empty []

theorem empty_signature_not_runtime_admitted : ¬ emptySignatureCell.RuntimeSupported := by
  simp [emptySignatureCell, CostStack.RuntimeSupported, CostSig.RuntimeValid]

theorem actual_empty_signature_receipt :
    (occurrenceOutputs RhoCalculus.Metabolic.spent actualReceipt.target).map
      (SignatureCodec.signatureRead (Ground := Nat)) = {(0 : CostSig Nat)} := by
  rw [actualReceipt, prefix_spent_signature_readout]
  rfl

theorem communication_does_not_create_funding :
    actualReceipt.execution.length = 2 ∧
      ((occurrenceOutputs RhoCalculus.Metabolic.spent actualReceipt.target).map
        (SignatureCodec.signatureRead (Ground := Nat))).sum = 0 ∧
      ¬ emptySignatureCell.RuntimeSupported := by
  refine ⟨actual_communications, ?_, empty_signature_not_runtime_admitted⟩
  rw [actual_empty_signature_receipt]
  simp

theorem no_admitted_empty_head (debit : DebitReadout Nat) : debit.head ≠ 0 :=
  debit.head_valid

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.ValidityControls
