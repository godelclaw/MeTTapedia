import Mettapedia.OSLF.Framework.RhoScopeAssayReceipts
import Mettapedia.GSLT.Causality.ProbeAssayRounds

/-!
# Paid probe rounds for arbitrary generated scopes on intrinsic rho names

Questions select two independently supplied decidable process predicates.
The actual generated-scope guard instantiates the existing delivery and
linear receiver protocol. Every response of a supplied occurrence path has
the offered name and requester, and receives a constructed dependent scope
receipt. Delivery and inspection prices remain declared schedules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeRounds

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationGeneratedScope
open RhoGeneratedScopeDecision RhoScopeAssayReceipts
open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory ProbeCampaign
open ComplementaryAssay (Verdict verdictOf)

universe q v w

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  equationClassDecision context Srt.nm

def protocol {Questions : Type q} {context : Ctx sig}
    (left right : Questions → Process context → Prop)
    [∀ question, DecidablePred (left question)] [∀ question, DecidablePred (right question)]
    (deliveryCost inspectionCost : Questions → Name context → Nat) :
    ProbeCampaign.Protocol Questions (Name context) where
  test question := guard (left question) (right question)
  deliveryCost := deliveryCost
  inspectionCost := inspectionCost

variable {Questions : Type q} {context : Ctx sig}
variable {Providers : Type v} {Clients : Type w}
variable [DecidableEq Providers] [DecidableEq Clients]
variable (left right : Questions → Process context → Prop)
variable [∀ question, DecidablePred (left question)] [∀ question, DecidablePred (right question)]
variable (deliveryCost inspectionCost : Questions → Name context → Nat)
variable {request : Request Questions (Name context) Providers Clients} {budget : Nat}

theorem response_guard
    (round : Round (protocol left right deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses) :
    response.2.1 = verdictOf (guard (left request.question) (right request.question) response.2.2.2) := by
  obtain ⟨value, _, same, _, _, _⟩ := round.response_sound response present
  rw [same]
  rfl

def responseReceipt
    (round : Round (protocol left right deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses) :
    DecisionReceipt (left request.question) (right request.question) response.2.2.2 response.2.1 :=
  Eq.mp (congrArg
    (fun branch => DecisionReceipt (left request.question) (right request.question) response.2.2.2 branch)
    (response_guard left right deliveryCost inspectionCost round response present).symm)
    (decisionReceipt (left request.question) (right request.question) response.2.2.2)

theorem response_origin_and_account
    (round : Round (protocol left right deliveryCost inspectionCost) request budget)
    (response : Response (Name context) Clients) (present : response ∈ round.responses) :
    response.1 = request.session ∧ response.2.2.1 = request.client ∧
      request.arrival = some response.2.2.2 ∧
      deliveryCost request.question response.2.2.2 + inspectionCost request.question response.2.2.2 ≤ budget ∧
      budget = round.remaining + deliveryCost request.question response.2.2.2 +
        inspectionCost request.question response.2.2.2 := by
  obtain ⟨value, offered, same, _, affordable, spent⟩ := round.response_sound response present
  rw [same]
  have account := round.ledger
  rw [spent] at account
  exact ⟨rfl, rfl, offered, affordable, by simpa only [protocol, Nat.add_assoc] using account⟩

theorem maximal_response_and_delivery
    (request : Request Questions (Name context) Providers Clients) (value : Name context)
    (offered : request.arrival = some value) (budget : Nat)
    (round : Round (protocol left right deliveryCost inspectionCost) request budget)
    (affordable : deliveryCost request.question value + inspectionCost request.question value ≤ budget)
    (maximal : AssayProbeDelivery.Maximal
      (guard (left request.question) (right request.question))
      (deliveryCost request.question) (inspectionCost request.question) round.endpoint) :
    round.responses =
      {(request.session, verdictOf (guard (left request.question) (right request.question) value),
        request.client, value)} ∧
      rightPart (leftPart round.endpoint) =
        {AssayProbeDelivery.ProbeResource.delivered request.session request.provider request.client value} ∧
      ((AssayProbeDelivery.paid (guard (left request.question) (right request.question))
        (deliveryCost request.question) (inspectionCost request.question)).pathEntries round.path).length = 2 ∧
      budget = round.remaining + deliveryCost request.question value + inspectionCost request.question value := by
  rcases request with ⟨question, session, provider, client, arrival⟩
  dsimp only at offered
  subst arrival
  obtain ⟨responses, entries, receipt, account⟩ := AssayProbeDelivery.maximal_affordable_verdict
    (guard (left question) (right question)) (deliveryCost question) (inspectionCost question)
    session provider client value budget affordable round.path maximal
  exact ⟨responses, receipt, entries, by simpa only [Round.remaining, Nat.add_assoc] using account⟩

end Mettapedia.OSLF.Framework.RhoScopeProbeRounds
