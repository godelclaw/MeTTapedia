import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicReflection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicSignatureCodec

/-!
# Complete operational controls for structural metabolic stacks

An acquired stack contains a repeated signing atom in its first cell and a
separate second signature. Two real debit cycles consume its cells in order.
The exact spent signatures and all five communications are retained. Empty
stacks cannot complete a debit, and spent messages cannot restart an exhausted
owner. These controls use the canonical signature codec and occurrence rules.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalBag LanguageDefGSLT ResourcePredation ResourceClaimHistory

private def encoding : Encoding (Cost.CostSig Nat) where
  code := Cost.Metabolic.SignatureCodec.signatureCode
  typed := fun head => Cost.Metabolic.SignatureCodec.signature_typed head []
  safe := Cost.Metabolic.SignatureCodec.signature_safe
  normalize := Cost.Metabolic.SignatureCodec.signature_normal
  substitution := Cost.Metabolic.SignatureCodec.signature_subst
  canonical := Cost.Metabolic.SignatureCodec.signature_canonical

def firstHead : Cost.CostSig Nat := {0, 0}
def secondHead : Cost.CostSig Nat := {1}
def fundedStack : Stack (Cost.CostSig Nat) := .cell firstHead (.cell secondHead .empty)

/-- The offered purse is environmental; the claimant and controller are owned. -/
private def originOf (pattern : Pattern) : Origin :=
  if pattern = canonicalize (offer encoding fundedStack) then .context else .computation

def initial : Configuration := annotate (acquisitionSource encoding fundedStack 2 []) originOf 17

def acquisitionReceipt : Acquisition encoding fundedStack 2 [] initial :=
  acquire encoding fundedStack 2 [] initial (annotate_inventory _ _ _)

def debitReceipt : Batch encoding fundedStack .empty [] acquisitionReceipt.claim.target :=
  batch encoding fundedStack .empty [] acquisitionReceipt.claim.target acquisitionReceipt.transferred

def execution : Execution initial debitReceipt.target :=
  acquisitionReceipt.execution.append debitReceipt.execution

theorem actual_source : inventory initial = fromProcess (acquisitionSource encoding fundedStack 2 []) :=
  annotate_inventory _ _ _

theorem initial_distinct : Distinct initial := annotate_distinct _ _ _

theorem five_actual_communications : execution.length = 5 := by
  rw [execution, Execution.append_length, acquisitionReceipt.execution_length, debitReceipt.length]
  rfl

theorem complete_claim_ledger : execution.claimedKeys.length = 5 ∧ execution.claimedKeys.Nodup := by
  constructor
  · unfold Execution.claimedKeys
    rw [List.length_map, Execution.claims_length, five_actual_communications]
  · exact execution.claimedKeys_nodup initial_distinct

theorem actual_public_history :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout initial) (readout debitReceipt.target) :=
  execution.public_history

theorem complete_initial_readout :
    CanonicalPayloadReadout (canonicalize (payload encoding fundedStack))
      [encoding.code firstHead, encoding.code secondHead] :=
  canonical_payload_readout encoding fundedStack

theorem recovered_order_and_multiplicity :
    [encoding.code firstHead, encoding.code secondHead].map
      (Cost.Metabolic.SignatureCodec.signatureRead (Ground := Nat)) = [{0, 0}, {1}] := by
  simp [encoding, firstHead, secondHead]

theorem acquisition_preserves_both_cells :
    inventory acquisitionReceipt.claim.target = fromProcess (live encoding fundedStack 2 []) ∧
      fundedStack.size = 2 := ⟨acquisitionReceipt.transferred, rfl⟩

theorem exact_final_spent_record :
    inventory debitReceipt.target = fromProcess (live encoding .empty 0 [secondHead, firstHead]) :=
  debitReceipt.remaining

theorem exact_structural_burn :
    fundedStack.size = (Stack.empty (Head := Cost.CostSig Nat)).size + 2 ∧
      (firstHead + secondHead).card = 3 := ⟨rfl, rfl⟩

theorem spent_cannot_restart : ∀ _ : ResourcePredation.Firing debitReceipt.target, False :=
  exhausted_live_has_no_firing encoding .empty [secondHead, firstHead]
    debitReceipt.target exact_final_spent_record

def emptyInitial : Configuration := annotate (live encoding .empty 3 []) (fun _ => .computation) 30

theorem empty_stack_never_completes_a_debit (first : ResourcePredation.Firing emptyInitial)
    (second : ResourcePredation.Firing first.target) : False :=
  empty_stack_second_firing_impossible encoding 2 [] emptyInitial (annotate_inventory _ _ _) first second

theorem empty_stack_actual_prefix_bound (target : Configuration)
    (partialExecution : Execution emptyInitial target) : partialExecution.length ≤ 1 := by
  cases partialExecution with
  | done => simp [Execution.length]
  | next first rest =>
      cases rest with
      | done => simp [Execution.length]
      | next second remainder => exact False.elim (empty_stack_never_completes_a_debit first second)

theorem debit_prefixes_are_bounded (target : Configuration)
    (partialExecution : Execution acquisitionReceipt.claim.target target) : partialExecution.length ≤ 4 :=
  live_execution_length_bound encoding 2 fundedStack [] acquisitionReceipt.claim.target
    target acquisitionReceipt.transferred partialExecution

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Controls
