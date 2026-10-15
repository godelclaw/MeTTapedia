import Mettapedia.OSLF.Framework.RhoScopeProbeRounds
import Mettapedia.GSLT.Causality.ProbeCampaignCompletion

/-!
# Constructed scope receipts for every actual paid campaign response

Sequential rounds pass their remaining purses to the next request. Public
packets are read from actual endpoints, and each reported scope verdict has
a constructed dependent receipt at the returned intrinsic name. Complete
affordable campaigns inherit the exact paid ledger and response count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeCampaigns

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback
open RhoScopeAssayReceipts RhoGeneratedScopeDecision
open Mettapedia.GSLT.Causality ProbeCampaign
open ComplementaryAssay (verdictOf)

universe q v w

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  equationClassDecision context Srt.nm

variable {Questions : Type q} {context : Ctx sig}
variable {Providers : Type v} {Clients : Type w}
variable [DecidableEq Providers] [DecidableEq Clients]
variable (left right : Questions → Process context → Prop)
variable [∀ question, DecidablePred (left question)] [∀ question, DecidablePred (right question)]
variable (deliveryCost inspectionCost : Questions → Name context → Nat)
variable {budget : Nat} {requests : List (Request Questions (Name context) Providers Clients)}

theorem response_guard
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (packet : Questions × Multiset (Response (Name context) Clients)) (listed : packet ∈ campaign.publicLog)
    (response : Response (Name context) Clients) (present : response ∈ packet.2) :
    response.2.1 = verdictOf (guard (left packet.1) (right packet.1) response.2.2.2) := by
  induction campaign with
  | nil _ => simp only [Campaign.publicLog, List.not_mem_nil] at listed
  | cons first rest ih =>
    rcases List.mem_cons.mp listed with same | later
    · subst packet
      exact RhoScopeProbeRounds.response_guard left right deliveryCost inspectionCost first response present
    · exact ih later

def responseReceipt
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (packet : Questions × Multiset (Response (Name context) Clients)) (listed : packet ∈ campaign.publicLog)
    (response : Response (Name context) Clients) (present : response ∈ packet.2) :
    DecisionReceipt (left packet.1) (right packet.1) response.2.2.2 response.2.1 :=
  Eq.mp (congrArg (fun branch => DecisionReceipt (left packet.1) (right packet.1) response.2.2.2 branch)
    (response_guard left right deliveryCost inspectionCost campaign packet listed response present).symm)
    (decisionReceipt (left packet.1) (right packet.1) response.2.2.2)

theorem response_semantics
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (packet : Questions × Multiset (Response (Name context) Clients)) (listed : packet ∈ campaign.publicLog)
    (response : Response (Name context) Clients) (present : response ∈ packet.2) :
    verdictPredicate (left packet.1) (right packet.1) response.2.2.2 response.2.1 :=
  decisionReceipt_sound (responseReceipt left right deliveryCost inspectionCost campaign packet listed response present)

theorem supplied_affordable_campaign
    (requests : List (Request Questions (Name context) Providers Clients)) (budget : Nat)
    (supplied : ∀ request ∈ requests, ∃ value, request.arrival = some value)
    (affordable : totalQuotedPrice (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests ≤ budget) :
    (executeCampaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests budget).completedTests =
        requests.length ∧
      (executeCampaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests budget).spent =
        totalQuotedPrice (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests ∧
      (executeCampaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests budget).remaining =
        budget - totalQuotedPrice (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests :=
  ProbeCampaign.supplied_affordable_campaign _ requests budget supplied affordable

end Mettapedia.OSLF.Framework.RhoScopeProbeCampaigns
