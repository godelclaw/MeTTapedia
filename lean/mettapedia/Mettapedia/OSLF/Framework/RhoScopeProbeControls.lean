import Mettapedia.OSLF.Framework.RhoScopeProbeLearner
import Mettapedia.OSLF.Framework.RhoScopeReceiptSearchControls

/-!
# Actual scope probe verdicts, underfunding and retained delivery

Two independently generated questions distinguish null-pair and output-pair
scopes. The same quoted null is confirmed by the former and refuted by the
latter. With insufficient inspection funding it is delivered but yields no
verdict. Absent offers also yield no verdict, at a different resource state.
The prices in this control are declared delivery and inspection schedules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback
open RhoEquationGeneratedScope RhoGeneratedScopeInventory
open RhoGeneratedScopeDecision RhoScopeMinimumReceipts RhoScopeAssayReceipts
open RhoScopeDecisionControls RhoScopeReceiptSearchControls
open Mettapedia.GSLT.Causality ResourceInteraction ProbeCampaign
open ComplementaryAssay (Verdict)

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  equationClassDecision context Srt.nm

local instance nullAtomDecision (context : Ctx sig) : DecidablePred (nullAtom (context := context)) :=
  fun process => show Decidable (process = zero context) from inferInstance

local instance outputAtomDecision (context : Ctx sig) : DecidablePred (outputAtom (context := context)) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

inductive Question where
  | nullPair
  | outputPair
  deriving DecidableEq

def left : Question → Process [] → Prop
  | .nullPair => nullAtom
  | .outputPair => outputAtom

def right : Question → Process [] → Prop
  | .nullPair => nullAtom
  | .outputPair => outputAtom

local instance leftDecision : ∀ question, DecidablePred (left question)
  | .nullPair => nullAtomDecision []
  | .outputPair => outputAtomDecision []

local instance rightDecision : ∀ question, DecidablePred (right question)
  | .nullPair => nullAtomDecision []
  | .outputPair => outputAtomDecision []

def nullName : Name [] := quote (zero [])

def scopeProtocol : Protocol Question (Name []) :=
  RhoScopeProbeRounds.protocol left right (fun _ _ => 2) (fun _ _ => 3)

def request (question : Question) (arrival : Option (Name [])) : Request Question (Name []) Nat Nat :=
  ⟨question, 0, 11, 22, arrival⟩

def run (question : Question) (arrival : Option (Name [])) (budget : Nat) :=
  completedRound scopeProtocol (request question arrival) budget

theorem null_question_accepts : guard (left .nullPair) (right .nullPair) nullName = true :=
  (guard_true_iff _ _ _).mpr (certificate_sound nullCertificate)

theorem output_question_rejects_null : guard (left .outputPair) (right .outputPair) nullName = false := by
  apply (guard_false_iff _ _ _).mpr
  exact output_scope_excludes_null

theorem output_question_accepts_actual_outputs :
    guard (left .outputPair) (right .outputPair) futureName = true := future_name_accepted

theorem affordable_null_confirmation :
    (run .nullPair (some nullName) 5).responses = {(0, Verdict.confirm, 22, nullName)} := by
  rw [run, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  rw [if_pos (show scopeProtocol.deliveryCost .nullPair nullName +
    scopeProtocol.inspectionCost .nullPair nullName ≤ 5 by decide)]
  change {(0, ComplementaryAssay.verdictOf (guard (left .nullPair) (right .nullPair) nullName), 22, nullName)} = _
  rw [null_question_accepts]
  rfl

theorem affordable_null_refutation :
    (run .outputPair (some nullName) 5).responses = {(0, Verdict.refute, 22, nullName)} := by
  rw [run, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  rw [if_pos (show scopeProtocol.deliveryCost .outputPair nullName +
    scopeProtocol.inspectionCost .outputPair nullName ≤ 5 by decide)]
  change {(0, ComplementaryAssay.verdictOf (guard (left .outputPair) (right .outputPair) nullName), 22, nullName)} = _
  rw [output_question_rejects_null]
  rfl

theorem underfunded_admitted_name_has_no_verdict :
    generated (left .nullPair) (right .nullPair) nullName ∧
      (run .nullPair (some nullName) 4).responses = 0 := by
  refine ⟨certificate_sound nullCertificate, ?_⟩
  rw [run, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  change (if 2 + 3 ≤ 4 then _ else 0) = 0
  exact if_neg (by decide)

theorem underfunded_inspection_retains_delivery :
    (run .nullPair (some nullName) 4).endpoint = AssayProbeDelivery.paidReceived 0 11 22 nullName 2 := by
  change (AssayProbeDelivery.execute (guard (left .nullPair) (right .nullPair))
    (fun _ => 2) (fun _ => 3) 0 11 22 (some nullName) 4).1 = _
  simp only [AssayProbeDelivery.execute, dif_pos (show 2 ≤ 4 by decide),
    dif_neg (show ¬ 3 ≤ 4 - 2 by decide)]
  rfl

theorem underfunded_delivery_receipt :
    rightPart (leftPart (run .nullPair (some nullName) 4).endpoint) =
      {AssayProbeDelivery.ProbeResource.delivered 0 11 22 nullName} := by
  rw [underfunded_inspection_retains_delivery, AssayProbeDelivery.paidReceived, leftPart_marking,
    AssayProbeDelivery.received, rightPart_marking]

theorem absent_offer_has_no_verdict (question : Question) (budget : Nat) :
    (run question none budget).responses = 0 := by
  rw [run, completedRound_responses]
  exact AssayProbeDelivery.observed_none _ _ _ _ _ _ _

theorem completed_null_ledger :
    (run .nullPair (some nullName) 5).remaining = 0 ∧ (run .nullPair (some nullName) 5).spent = 5 := by
  obtain ⟨_, spent, remaining⟩ := completed_round_price scopeProtocol (request .nullPair (some nullName))
    5 nullName rfl (by decide)
  exact ⟨remaining, spent⟩

end Mettapedia.OSLF.Framework.RhoScopeProbeControls
