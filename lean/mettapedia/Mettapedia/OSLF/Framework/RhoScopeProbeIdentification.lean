import Mettapedia.OSLF.Framework.RhoScopeProbeLearner

/-!
# Identification by actually answered separating scope questions

Independently supplied scope questions separate a finite prior when their
generated predicates differ on each alternative and the actual offered name.
Full completion earns those answered questions from actual paid paths.
Affordable supplied campaigns then identify the offered name within that
prior. Neither prior coverage nor semantic separation is manufactured by the
controller, and this result concerns the declared scope observations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeIdentification

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationGeneratedScope
open Mettapedia.GSLT.Causality ProbeCampaign
open FiniteAssayLearner RhoScopeProbeLearner

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

theorem complete_separating_campaign_identifies
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (candidates : Finset (Name context)) (actual : Name context) (initial : actual ∈ candidates)
    (offers : ∀ request ∈ requests, request.arrival = some actual)
    (finished : campaign.completedTests = requests.length)
    (covers : ∀ candidate ∈ candidates, candidate ≠ actual → ∃ request ∈ requests,
      ¬ (generated (left request.question) (right request.question) candidate ↔
        generated (left request.question) (right request.question) actual)) :
    learn (prediction left right) campaign candidates = {actual} := by
  have retained := actual_candidate_survives left right deliveryCost inspectionCost
    campaign candidates actual initial offers
  have actualCompatible := ((learn_mem _ campaign candidates actual).mp retained).2
  apply identified_by_responses _ campaign candidates actual initial actualCompatible
  intro candidate held different
  obtain ⟨request, requested, distinguish⟩ := covers candidate held different
  obtain ⟨packet, listed, sameQuestion, one⟩ := campaign.completed_member_responded finished request requested
  have notQuiet : packet.2 ≠ 0 := by
    intro quiet
    rw [quiet, Multiset.card_zero] at one
    omega
  obtain ⟨response, present⟩ := Multiset.exists_mem_of_ne_zero notQuiet
  refine ⟨packet, listed, response, present, ?_⟩
  have actualAnswer := actualCompatible packet listed response present
  rw [sameQuestion] at actualAnswer ⊢
  intro contrary
  have samePrediction : prediction left right candidate request.question =
      prediction left right actual request.question := contrary.trans actualAnswer.symm
  apply distinguish
  rw [← prediction_truth left right candidate request.question,
    ← prediction_truth left right actual request.question, samePrediction]

theorem supplied_affordable_scope_identifies
    (requests : List (Request Questions (Name context) Providers Clients)) (budget : Nat)
    (candidates : Finset (Name context)) (actual : Name context) (initial : actual ∈ candidates)
    (offers : ∀ request ∈ requests, request.arrival = some actual)
    (affordable : totalQuotedPrice (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests ≤ budget)
    (covers : ∀ candidate ∈ candidates, candidate ≠ actual → ∃ request ∈ requests,
      ¬ (generated (left request.question) (right request.question) candidate ↔
        generated (left request.question) (right request.question) actual)) :
    learn (prediction left right)
      (executeCampaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) requests budget)
      candidates = {actual} := by
  have supplied : ∀ request ∈ requests, ∃ value, request.arrival = some value :=
    fun request listed => ⟨actual, offers request listed⟩
  obtain ⟨finished, _, _⟩ := RhoScopeProbeCampaigns.supplied_affordable_campaign
    left right deliveryCost inspectionCost requests budget supplied affordable
  exact complete_separating_campaign_identifies left right deliveryCost inspectionCost
    _ candidates actual initial offers finished covers

end Mettapedia.OSLF.Framework.RhoScopeProbeIdentification
