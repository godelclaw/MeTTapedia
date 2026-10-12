import Mettapedia.OSLF.Framework.RhoGroundedScopeReceiptSubstitution

/-!
# Native grounded verdicts on supplied paid probe responses

The existing paid protocol supplies the response, session, requester and
purse ledger. A supplied ground origin promotes its constructed scope
receipt to the complete native verdict. Confirmation retains its whole
minimum certificate; native refutation excludes certificates at every
future substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoGroundedScopeProbeReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates BindingGroundedPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution
open RhoScopeAssayReceipts RhoGroundedScopeGuard
open Mettapedia.GSLT.Causality ResourceInteraction ProbeCampaign
open ComplementaryAssay (Verdict)

universe q v w

noncomputable section

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  RhoIntrinsicReadback.equationClassDecision context Srt.nm

variable {Questions : Type q} {context : Ctx sig}
variable {Providers : Type v} {Clients : Type w}
variable [DecidableEq Providers] [DecidableEq Clients]
variable (left right : Questions → Predicate model Srt.pr)
variable [∀ question : Questions, ∀ context : Ctx sig, DecidablePred ((left question).holds (Γ := context))]
variable [∀ question : Questions, ∀ context : Ctx sig, DecidablePred ((right question).holds (Γ := context))]
variable (deliveryCost inspectionCost : Questions → Name context → Nat)
variable {request : Request Questions (Name context) Providers Clients} {budget : Nat}

def responseReceipt
    (round : Round (RhoScopeProbeRounds.protocol
      (fun question => (left question).holds) (fun question => (right question).holds)
      deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses)
    (origin : GroundOrigin (A := model) (sort := Srt.nm) response.2.2.2) :
    NativeDecisionReceipt (left request.question) (right request.question) response.2.2.2 response.2.1 :=
  promote (left request.question) (right request.question)
    (RhoScopeProbeRounds.responseReceipt
      (fun question => (left question).holds) (fun question => (right question).holds)
      deliveryCost inspectionCost round response present) origin

theorem refuted_response_excludes_every_future
    (round : Round (RhoScopeProbeRounds.protocol
      (fun question => (left question).holds) (fun question => (right question).holds)
      deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses)
    (origin : GroundOrigin (A := model) (sort := Srt.nm) response.2.2.2)
    (refuted : response.2.1 = Verdict.refute)
    (future : Ctx sig) (env : Environment sig (TermQ rhoSourceE) context future) :
    ¬ generated (left request.question).holds (right request.question).holds
      (model.substitution.substitute env response.2.2.2) := by
  have nativeSound := (responseReceipt left right deliveryCost inspectionCost
    round response present origin).sound
  rw [refuted] at nativeSound
  exact nativeSound future env

theorem native_response_keeps_account
    (round : Round (RhoScopeProbeRounds.protocol
      (fun question => (left question).holds) (fun question => (right question).holds)
      deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses)
    (origin : GroundOrigin (A := model) (sort := Srt.nm) response.2.2.2) :
    (responseReceipt left right deliveryCost inspectionCost round response present origin).origin = origin ∧
      response.1 = request.session ∧ response.2.2.1 = request.client ∧
      request.arrival = some response.2.2.2 ∧
      deliveryCost request.question response.2.2.2 + inspectionCost request.question response.2.2.2 ≤ budget ∧
      budget = round.remaining + deliveryCost request.question response.2.2.2 +
        inspectionCost request.question response.2.2.2 :=
  ⟨rfl, RhoScopeProbeRounds.response_origin_and_account
    (fun question => (left question).holds) (fun question => (right question).holds)
    deliveryCost inspectionCost round response present⟩

end

end Mettapedia.OSLF.Framework.RhoGroundedScopeProbeReceipts
