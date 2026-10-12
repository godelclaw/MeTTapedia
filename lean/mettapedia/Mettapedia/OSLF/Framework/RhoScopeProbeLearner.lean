import Mettapedia.OSLF.Framework.RhoScopeProbeCampaigns
import Mettapedia.OSLF.Framework.FiniteAssayLearner

/-!
# Funded scope learning over actual intrinsic rho names

Finite candidates predict the generated-scope answers of the declared
questions. Revision consumes public responses of retained paid occurrence
paths. Confirmation removes a candidate excluded by that scope; refutation
removes an admitted candidate. A supplied actual candidate survives, while
candidates agreeing on every declared scope remain observationally tied.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeProbeLearner

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoEquationGeneratedScope
open RhoGeneratedScopeDecision
open Mettapedia.GSLT.Causality ProbeCampaign
open ComplementaryAssay (Verdict)
open FiniteAssayLearner

universe q v w

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  equationClassDecision context Srt.nm

variable {Questions : Type q} {context : Ctx sig}
variable (left right : Questions → Process context → Prop)
variable [∀ question, DecidablePred (left question)] [∀ question, DecidablePred (right question)]

def prediction (candidate : Name context) (question : Questions) : Bool :=
  guard (left question) (right question) candidate

theorem prediction_truth (candidate : Name context) (question : Questions) :
    prediction left right candidate question = true ↔ generated (left question) (right question) candidate :=
  guard_true_iff _ _ _

variable {Providers : Type v} {Clients : Type w}

theorem confirmed_response_removes_excluded_candidate
    (question : Questions) (candidates : Finset (Name context)) (candidate : Name context)
    (responses : Multiset (Response (Name context) Clients)) (response : Response (Name context) Clients)
    (present : response ∈ responses) (confirmed : response.2.1 = .confirm)
    (excluded : ¬ generated (left question) (right question) candidate) :
    candidate ∉ revise (prediction left right) candidates question responses := by
  apply response_removes _ _ _ _ _ response present
  have negative := (guard_false_iff (left question) (right question) candidate).mpr excluded
  rw [prediction, negative, confirmed]
  exact Bool.false_ne_true

theorem refuted_response_removes_admitted_candidate
    (question : Questions) (candidates : Finset (Name context)) (candidate : Name context)
    (responses : Multiset (Response (Name context) Clients)) (response : Response (Name context) Clients)
    (present : response ∈ responses) (refuted : response.2.1 = .refute)
    (admitted : generated (left question) (right question) candidate) :
    candidate ∉ revise (prediction left right) candidates question responses := by
  apply response_removes _ _ _ _ _ response present
  have positive := (guard_true_iff (left question) (right question) candidate).mpr admitted
  rw [prediction, positive, refuted]
  decide

variable [DecidableEq Providers] [DecidableEq Clients]
variable (deliveryCost inspectionCost : Questions → Name context → Nat)
variable {budget : Nat} {requests : List (Request Questions (Name context) Providers Clients)}

theorem actual_candidate_survives
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (candidates : Finset (Name context)) (actual : Name context) (initial : actual ∈ candidates)
    (offers : ∀ request ∈ requests, request.arrival = some actual) :
    actual ∈ learn (prediction left right) campaign candidates := by
  apply offered_candidate_survives _ campaign candidates actual initial
  intro request listed value arrived
  have same : value = actual := Option.some.inj (arrived.symm.trans (offers request listed))
  subst value
  rfl

theorem same_scope_predictions {first second : Name context}
    (same : ∀ question, generated (left question) (right question) first ↔
      generated (left question) (right question) second) (question : Questions) :
    prediction left right first question = prediction left right second question := by
  apply Bool.eq_iff_iff.mpr
  rw [prediction_truth, prediction_truth]
  exact same question

theorem same_scope_retention
    (campaign : Campaign (RhoScopeProbeRounds.protocol left right deliveryCost inspectionCost) budget requests)
    (candidates : Finset (Name context)) {first second : Name context}
    (firstHeld : first ∈ candidates) (secondHeld : second ∈ candidates)
    (same : ∀ question, generated (left question) (right question) first ↔
      generated (left question) (right question) second) :
    first ∈ learn (prediction left right) campaign candidates ↔
      second ∈ learn (prediction left right) campaign candidates := by
  rw [learn_mem, learn_mem]
  simp only [firstHeld, secondHeld, true_and]
  have agreement : ∀ (question : Questions) (responses : Multiset (Response (Name context) Clients)),
      Compatible (prediction left right) first question responses ↔
        Compatible (prediction left right) second question responses := by
    intro question responses
    unfold Compatible
    rw [same_scope_predictions left right same question]
  simp only [agreement]

end Mettapedia.OSLF.Framework.RhoScopeProbeLearner
