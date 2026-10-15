import Mettapedia.OSLF.Framework.RhoScopedInstrumentQuestionTranslation
import Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssays

/-!
# Native paid assay answers in the original binding observer system

An actual native occurrence supplies an identity-labelled proper action at
the original interfaces. A paid public answer supplies the corresponding
translated finite-stage observer certificate at its exact target. The
native witness, complete firing, public routing data and resource ledger
remain separate retained data throughout this comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentAssayReadout

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open DisplayedPresheafTransport
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls ScopedEncoding
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedInstrumentProperBase
open RhoScopedFundedInspection RhoScopedFundedNativeAssays RhoScopedInstrumentQuestionTranslation
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

def ObserverCertificate (admitted : SourceRule → Prop) {context : Ctx sig}
    (question : Question context) (verdict : Verdict) (endpoint : Process context) : Prop :=
  match verdict with
  | .confirm => ScopedInstruments.Holds (base admitted) (stage question) (Quotient.out endpoint)
  | .refute => ¬ ScopedInstruments.Holds (base admitted) (stage question) (Quotient.out endpoint)

theorem observer_certificate_iff_original (admitted : SourceRule → Prop) {context : Ctx sig}
    (question : Question context) (verdict : Verdict) (endpoint : Process context) :
    ObserverCertificate admitted question verdict endpoint ↔ StageCertificate admitted question verdict endpoint := by
  have comparison := stage_truth admitted question (Quotient.out endpoint)
  simp only [project, Quotient.out_eq] at comparison
  cases verdict with
  | confirm => exact comparison
  | refute => exact not_congr comparison

theorem question_needs_no_structural_permission {context : Ctx sig}
    (question : Question context) (opened : Constructor sig → Prop) :
    SortedInstrumentCongruence.Formula.Allowed opened (stage question) :=
  translation_allowed _ _ opened

variable {context : Ctx sig} (admitted : SourceRule → Prop)
variable (family : DisplayedFamily (RhoScopedEventPresheaf.terms .pr))

theorem native_reaction_is_original_proper
    (native : NativeReceipt admitted family (context := context)) :
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, zero context⟩ (Quotient.out native.1)
        (Quotient.out (currentTarget admitted family native)) := by
  apply (proper_iff_complete_firing admitted (zero context) _ _).mpr
  have sourceRead : project (Quotient.out (native.1 : Process context)) = native.1 :=
    Quotient.out_eq (native.1 : Process context)
  have targetRead : project (Quotient.out (currentTarget admitted family native)) =
      currentTarget admitted family native := Quotient.out_eq _
  rw [sourceRead, targetRead]
  exact ⟨currentReaction admitted family native⟩

universe p c
variable {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
variable {rates : SourceRule → Nat} {native : NativeReceipt admitted family (context := context)}
variable {deliveryCost : Question context → Process context → Nat}
variable {request : Request (Question context) (Process context) Providers Clients} {budget : Nat}

theorem paid_native_answer_observer_certificate
    (receipt : RhoScopedFundedNativeAssays.Receipt admitted family rates native deliveryCost request budget)
    (response : Response (Process context) Clients) (reported : response ∈ receipt.responses) :
    ∃ answer : Bool,
      request.arrival = some (currentTarget admitted family native) ∧
      response = (request.session, verdictOf answer, request.client, currentTarget admitted family native) ∧
      ObserverCertificate admitted request.question (verdictOf answer) (currentTarget admitted family native) ∧
      receipt.spent = reactionPrice admitted family rates native +
        deliveryCost request.question (currentTarget admitted family native) +
        (protocol admitted context deliveryCost).inspectionCost request.question
          (currentTarget admitted family native) := by
  obtain ⟨answer, arrival, readout, certificate, charges⟩ := receipt.current_target_certificate response reported
  exact ⟨answer, arrival, readout,
    (observer_certificate_iff_original admitted request.question _ _).mpr certificate, charges⟩

end Mettapedia.OSLF.Framework.RhoScopedInstrumentAssayReadout
