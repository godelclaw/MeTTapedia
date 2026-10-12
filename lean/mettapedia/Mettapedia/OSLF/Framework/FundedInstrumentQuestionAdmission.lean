import Mettapedia.OSLF.Framework.InstrumentQuestionAdmission
import Mettapedia.OSLF.Framework.StructuralFundedAssayControls

/-!
# Instrument admission before an actual funded assay

The admission checker constructs a protocol question while preserving the
request's session, provider, client and offered tree. Actual response
prefixes earn the independent structural answer, instrument permission,
affordability and exact purse balance.

The controller distinguishes rejected admission from an admitted request
with no response. Its controls hold the formula and offered tree fixed:
the complete kit answers when funded, stays quiet when underfunded, and
the empty kit rejects the request regardless of funding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission

open InstrumentObservations InstrumentQuestionAdmission
open Mettapedia.GSLT.Causality ProbeCampaign ResourceInteraction
open ComplementaryAssay (verdictOf)

universe u v w

variable {Symbols : Type u} {arity : Symbols → Nat}
variable {Providers : Type v} {Clients : Type w}

def prepare? (opened : Policy Symbols) [DecidablePred opened]
    (request : Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients) :
    Option (Request (FundedStructuralLearner.Question (arity := arity) opened) (Tree Symbols arity) Providers Clients) :=
  (question? opened request.question).map fun question =>
    { question := question, session := request.session, provider := request.provider,
      client := request.client, arrival := request.arrival }

theorem prepare?_sound (opened : Policy Symbols) [DecidablePred opened]
    (request : Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients)
    (prepared : Request (FundedStructuralLearner.Question (arity := arity) opened) (Tree Symbols arity) Providers Clients)
    (produced : prepare? opened request = some prepared) :
    AdmittedFormula opened request.question ∧ prepared.question.val = request.question ∧
      prepared.session = request.session ∧ prepared.provider = request.provider ∧
        prepared.client = request.client ∧ prepared.arrival = request.arrival := by
  cases admitted : question? opened request.question with
  | none =>
      simp only [prepare?, admitted, Option.map_none] at produced
      cases produced
  | some question =>
      let built : Request (FundedStructuralLearner.Question (arity := arity) opened)
          (Tree Symbols arity) Providers Clients :=
        { question := question, session := request.session, provider := request.provider,
          client := request.client, arrival := request.arrival }
      have exactRequest : built = prepared := Option.some.inj
        (show some built = some prepared by
          simpa only [prepare?, admitted, Option.map_some, built] using produced)
      subst prepared
      have formula := question?_readout opened request.question question admitted
      exact ⟨formula ▸ question.property, formula, rfl, rfl, rfl, rfl⟩

variable [DecidableEq Symbols] [DecidableEq Providers] [DecidableEq Clients]

def protocol (opened : Policy Symbols)
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat) :
    Protocol (FundedStructuralLearner.Question (arity := arity) opened) (Tree Symbols arity) :=
  FundedStructuralLearner.protocol opened (fun question tree => deliveryCost question.val tree)

theorem prepared_response (opened : Policy Symbols) [DecidablePred opened]
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat)
    (request : Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients)
    (prepared : Request (FundedStructuralLearner.Question (arity := arity) opened) (Tree Symbols arity) Providers Clients)
    (produced : prepare? opened request = some prepared) {budget : Nat}
    (round : Round (protocol opened deliveryCost) prepared budget)
    (response : Response (Tree Symbols arity) Clients) (present : response ∈ round.responses) :
    AdmittedFormula opened request.question ∧
      ∃ value, request.arrival = some value ∧
        response = (request.session, verdictOf (evaluate request.question value), request.client, value) ∧
        deliveryCost request.question value + traversalWork request.question value ≤ budget ∧
        budget = round.remaining + deliveryCost request.question value + traversalWork request.question value := by
  obtain ⟨permission, formula, session, _, client, arrival⟩ := prepare?_sound opened request prepared produced
  obtain ⟨value, offered, answer, _, affordable, spent⟩ := round.response_sound response present
  have cost : deliveryCost request.question value + traversalWork request.question value ≤ budget := by
    simpa only [protocol, FundedStructuralLearner.protocol, formula, inspect_work] using affordable
  have account : round.spent = deliveryCost request.question value + traversalWork request.question value := by
    simpa only [protocol, FundedStructuralLearner.protocol, formula, inspect_work] using spent
  refine ⟨permission, value, arrival ▸ offered, ?_, cost, ?_⟩
  · simpa only [protocol, FundedStructuralLearner.protocol, formula, session, client,
      inspect_readout] using answer
  · have conserved := round.ledger
    rw [account] at conserved
    omega

def execute? (opened : Policy Symbols) [DecidablePred opened]
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat)
    (request : Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients)
    (budget : Nat) : Option (Multiset (Response (Tree Symbols arity) Clients)) :=
  (prepare? opened request).map fun prepared =>
    (completedRound (protocol opened deliveryCost) prepared budget).responses

theorem execute?_readout (opened : Policy Symbols) [DecidablePred opened]
    (deliveryCost : Formula Symbols arity → Tree Symbols arity → Nat)
    (request : Request (Formula Symbols arity) (Tree Symbols arity) Providers Clients)
    (budget : Nat) :
    execute? opened deliveryCost request budget =
      if check opened request.question = true then
        some (AssayProbeDelivery.observed (evaluate request.question)
          (deliveryCost request.question) (traversalWork request.question)
          request.session request.provider request.client request.arrival budget)
      else none := by
  unfold execute? prepare? question?
  split_ifs with checked
  · simp only [Option.map_some, completedRound_responses, protocol, FundedStructuralLearner.protocol]
    have answer : (fun tree : Tree Symbols arity => (inspect request.question tree).1) =
        evaluate request.question := funext fun tree => congrArg Prod.fst (inspect_readout _ tree)
    have work : (fun tree : Tree Symbols arity => (inspect request.question tree).2) =
        traversalWork request.question := funext fun tree => inspect_work _ tree
    rw [answer, work]
  · rfl

namespace Controls

open InstrumentObservations.AssayControls

def completeKit : Policy Bool := fun constructor => constructor ∈ ({false, true} : Finset Bool)
def emptyKit : Policy Bool := fun constructor => constructor ∈ (∅ : Finset Bool)
def rootOnlyKit : Policy Bool := fun constructor => constructor ∈ ({true} : Finset Bool)

instance complete_decidable : DecidablePred completeKit := fun constructor =>
  inferInstanceAs (Decidable (constructor ∈ ({false, true} : Finset Bool)))
instance empty_decidable : DecidablePred emptyKit := fun constructor =>
  inferInstanceAs (Decidable (constructor ∈ (∅ : Finset Bool)))
instance root_only_decidable : DecidablePred rootOnlyKit := fun constructor =>
  inferInstanceAs (Decidable (constructor ∈ ({true} : Finset Bool)))

def request : Request (Formula Bool InstrumentObservations.AssayControls.arity)
    (Tree Bool InstrumentObservations.AssayControls.arity) Nat Nat where
  question := pairedFormula
  session := 20
  provider := 11
  client := 7
  arrival := some paired

theorem capability_checks_complete_children :
    check completeKit pairedFormula = true ∧ check emptyKit pairedFormula = false := by
  decide

theorem root_permission_does_not_supply_child_instruments :
    rootOnlyKit true ∧ check rootOnlyKit pairedFormula = false := by decide

theorem funded_complete_answer :
    execute? completeKit (fun _ _ => 0) request 3 = some {(20, .confirm, 7, paired)} := by
  rw [execute?_readout]
  decide

theorem admitted_but_underfunded_is_quiet :
    execute? completeKit (fun _ _ => 0) request 2 = some 0 := by
  rw [execute?_readout]
  decide

theorem funding_does_not_supply_missing_instrument (budget : Nat) :
    execute? emptyKit (fun _ _ => 0) request budget = none := by
  rw [execute?_readout]
  have rejected := capability_checks_complete_children.2
  simp only [request, rejected, Bool.false_eq_true, ↓reduceIte]

end Controls

end Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission
