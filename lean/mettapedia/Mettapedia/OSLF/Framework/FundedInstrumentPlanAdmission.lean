import Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission

/-!
# Ordered authored assay plans and the funded structural learner

Admission traverses the supplied request list without filtering, merging
or reordering occurrences. Successful preparation retains every formula,
session, provider, client and offer. A denied request rejects the plan.

The actual funded campaign on a prepared plan is joined to the existing
learner through the earned offer comparison. A correctly predicted offered
candidate survives arbitrary actual prefixes. Inspection positivity bounds
completed tests, while the campaign retains its exact occurrence ledger.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedInstrumentPlanAdmission

open InstrumentObservations FundedInstrumentQuestionAdmission
open Mettapedia.GSLT.Causality ProbeCampaign

universe u v w

variable {Symbols : Type u} {arity : Symbols → Nat}
variable {Providers : Type v} {Clients : Type w}

abbrev AuthoredRequest := Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients
abbrev PreparedRequest (opened : Policy Symbols) :=
  Request (FundedStructuralLearner.Question (arity := arity) opened) (Tree Symbols arity) Providers Clients

def eraseRequest {opened : Policy Symbols}
    (request : PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened) :
    AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients) where
  question := request.question.val
  session := request.session
  provider := request.provider
  client := request.client
  arrival := request.arrival

def preparePlan? (opened : Policy Symbols) [DecidablePred opened] :
    List (AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients)) →
      Option (List (PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened))
  | [] => some []
  | request :: rest => do
      let prepared ← prepare? opened request
      let next ← preparePlan? opened rest
      pure (prepared :: next)

theorem prepare?_erasure (opened : Policy Symbols) [DecidablePred opened]
    (request : AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients))
    (prepared : PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened)
    (produced : prepare? opened request = some prepared) : eraseRequest prepared = request := by
  obtain ⟨_, formula, session, provider, client, arrival⟩ := prepare?_sound opened request prepared produced
  cases request
  cases prepared
  simp only [eraseRequest] at *
  congr

theorem plan_erasure (opened : Policy Symbols) [DecidablePred opened]
    (requests : List (AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients)))
    (prepared : List (PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened))
    (produced : preparePlan? opened requests = some prepared) : prepared.map eraseRequest = requests := by
  induction requests generalizing prepared with
  | nil =>
      have same : [] = prepared := Option.some.inj produced
      subst prepared
      rfl
  | cons request rest inductionHypothesis =>
      cases head : prepare? opened request with
      | none => simp [preparePlan?, head] at produced
      | some first =>
          cases tail : preparePlan? opened rest with
          | none => simp [preparePlan?, head, tail] at produced
          | some next =>
              have same : first :: next = prepared := by simpa [preparePlan?, head, tail] using produced
              subst prepared
              simp only [List.map_cons, prepare?_erasure opened request first head,
                inductionHypothesis next tail]

theorem plan_occurrences (opened : Policy Symbols) [DecidablePred opened]
    (requests : List (AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients)))
    (prepared : List (PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened))
    (produced : preparePlan? opened requests = some prepared) : prepared.length = requests.length := by
  have same := congrArg List.length (plan_erasure opened requests prepared produced)
  simpa only [List.length_map] using same

variable [DecidableEq Symbols] [DecidableEq Providers] [DecidableEq Clients]

theorem authored_candidate_survives (opened : Policy Symbols) [DecidablePred opened]
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat)
    (requests : List (AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients)))
    (prepared : List (PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened))
    (produced : preparePlan? opened requests = some prepared) {budget : Nat}
    (campaign : Campaign (protocol opened deliveryCost) budget prepared)
    (candidates : Finset (Tree Symbols arity)) (actual : Tree Symbols arity)
    (initial : actual ∈ candidates) (offers : ∀ request ∈ requests, request.arrival = some actual) :
    actual ∈ FiniteAssayLearner.learn (FundedStructuralLearner.prediction opened) campaign candidates := by
  apply FundedStructuralLearner.actual_candidate_survives opened
    (fun question tree => deliveryCost question.val tree) campaign candidates actual initial
  intro request member
  have original : eraseRequest request ∈ requests := by
    rw [← plan_erasure opened requests prepared produced]
    exact List.mem_map.mpr ⟨request, member, rfl⟩
  exact offers (eraseRequest request) original

theorem authored_campaign_bounds (opened : Policy Symbols) [DecidablePred opened]
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat)
    (requests : List (AuthoredRequest (arity := arity) (Providers := Providers) (Clients := Clients)))
    (prepared : List (PreparedRequest (arity := arity) (Providers := Providers) (Clients := Clients) opened))
    (produced : preparePlan? opened requests = some prepared) {budget : Nat}
    (campaign : Campaign (protocol opened deliveryCost) budget prepared) :
    campaign.completedTests ≤ budget ∧ campaign.completedTests ≤ requests.length ∧
      budget = campaign.remaining + campaign.spent :=
  ⟨FundedStructuralLearner.campaign_test_bound opened
      (fun question tree => deliveryCost question.val tree) campaign,
    (plan_occurrences opened requests prepared produced) ▸ campaign.completedTests_le_requests,
    campaign.ledger⟩

namespace Controls

open FundedInstrumentQuestionAdmission.Controls

def twoRequests := [request, {request with session := 21}]

theorem repeated_question_occurrences_are_admitted :
    (preparePlan? completeKit twoRequests).isSome = true := by decide

theorem two_sessions_remain_in_order
    (prepared : List (PreparedRequest (arity := InstrumentObservations.AssayControls.arity)
      (Providers := Nat) (Clients := Nat) completeKit))
    (produced : preparePlan? completeKit twoRequests = some prepared) :
    prepared.length = 2 ∧ prepared.map Request.session = [20, 21] := by
  have preserved := plan_erasure completeKit twoRequests prepared produced
  constructor
  · exact plan_occurrences completeKit twoRequests prepared produced
  · have sessions := congrArg (List.map Request.session) preserved
    simpa only [List.map_map, eraseRequest, Function.comp_def, twoRequests,
      List.map_cons, List.map_nil, request] using sessions

theorem rejected_request_is_not_filtered : preparePlan? emptyKit twoRequests = none := by
  have head : prepare? emptyKit request = none := by
    unfold prepare? InstrumentQuestionAdmission.question?
    have rejected := capability_checks_complete_children.2
    simp only [request, rejected, Bool.false_eq_true, ↓reduceDIte, Option.map_none]
  simp [twoRequests, preparePlan?, head]

end Controls

end Mettapedia.OSLF.Framework.FundedInstrumentPlanAdmission
