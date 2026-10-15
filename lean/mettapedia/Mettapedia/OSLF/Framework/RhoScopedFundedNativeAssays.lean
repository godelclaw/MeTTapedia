import Mettapedia.OSLF.Framework.RhoScopedNativeRateHistory
import Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts

/-!
# Configured original reaction funding followed by paid target inspection

The supplied native certificate determines an actual original identity-labelled
reaction and its complete target witness. A separate original paid occurrence
history funds that reaction. The remaining budget then funds delivery and an
independently executed modal instruction prefix at its exact target.

The combined ledger includes all three declared charges. A verdict requires
completed inspection; it does not follow from a native certificate or a funded
reaction alone. These are the declared resource and instruction presentations,
not an implementation cost claim or a covariance theorem for arbitrary tests.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssays

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedParallelReactiveSystem RhoScopedParallelInventory
open RhoScopedDependentEventFutures RhoScopedNativeRateHistory RhoScopedFundedInspection
open DisplayedPresheafComprehension DisplayedPresheafTransport PresheafEventCertificates
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

universe p c
variable {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _
variable {context : Ctx sig}
variable (admitted : SourceRule → Prop)
variable (family : DisplayedFamily (RhoScopedEventPresheaf.terms .pr))

abbrev AtContext := Opposite.op (⟨context⟩ : Syntactic.Ctxt sig)

abbrev NativeReceipt := (totalSpace (certificates admitted family)).obj (AtContext (context := context))

def currentTarget (receipt : NativeReceipt admitted family (context := context)) : Process context :=
  ((targetReadout admitted family).app AtContext receipt).1

def currentReaction (receipt : NativeReceipt admitted family (context := context)) :
    RhoScopedParallelReactiveSystem.Firing (rules := sourceRules) (admitted := admitted)
      receipt.1 (zero context) (currentTarget admitted family receipt) where
  root := (nativeEvent admitted family receipt).1
  surrounding := (nativeEvent admitted family receipt).2
  square := by
    have sourceReadout := congrArg (fun map => map.app AtContext receipt)
      ((span admitted).eventReadout_source family)
    change join (nativeEvent admitted family receipt).1.source
      (nativeEvent admitted family receipt).2 = receipt.1 at sourceReadout
    exact (join_zero_right receipt.1).trans sourceReadout.symm
  least := by rw [read_zero, Multiset.zero_inter]
  target := by
    have targetReadout := congrArg (fun map => map.app AtContext receipt)
      ((span admitted).resultReadout_target family)
    exact targetReadout

def reactionPrice (rates : SourceRule → Nat)
    (receipt : NativeReceipt admitted family (context := context)) : Nat :=
  rates ((receiptOrigin admitted family).app AtContext receipt).val

structure Receipt (rates : SourceRule → Nat)
    (native : NativeReceipt admitted family (context := context))
    (deliveryCost : Question context → Process context → Nat)
    (request : Request (Question context) (Process context) Providers Clients) (budget : Nat) where
  funding : NativePaid admitted family rates native budget
  inspection : RhoScopedReactionAssayReceipts.Receipt admitted deliveryCost request
    (budget - reactionPrice admitted family rates native) native.1 (zero context)
    (currentTarget admitted family native)
  retainedReaction : inspection.reaction = currentReaction admitted family native

variable {admitted family}
variable {rates : SourceRule → Nat} {native : NativeReceipt admitted family (context := context)}
variable {deliveryCost : Question context → Process context → Nat}
variable {request : Request (Question context) (Process context) Providers Clients} {budget : Nat}

namespace Receipt

def inspect (reactionAffordable : reactionPrice admitted family rates native ≤ budget)
    (offered : request.arrival = some (currentTarget admitted family native))
    (deliveryAffordable : deliveryCost request.question (currentTarget admitted family native) ≤
      budget - reactionPrice admitted family rates native) :
    Receipt admitted family rates native deliveryCost request budget where
  funding := (native_paid_iff admitted family rates native budget).mpr reactionAffordable |>.some
  inspection := RhoScopedReactionAssayReceipts.Receipt.inspectTarget
    (currentReaction admitted family native) offered deliveryAffordable
  retainedReaction := rfl

def responses (receipt : Receipt admitted family rates native deliveryCost request budget) :
    Multiset (Response (Process context) Clients) := receipt.inspection.responses

def spent (receipt : Receipt admitted family rates native deliveryCost request budget) : Nat :=
  reactionPrice admitted family rates native + receipt.inspection.spent

def remaining (receipt : Receipt admitted family rates native deliveryCost request budget) : Nat :=
  receipt.inspection.remaining

theorem complete_original_event_retained
    (receipt : Receipt admitted family rates native deliveryCost request budget) :
    receipt.inspection.reaction.root = (nativeEvent admitted family native).1 ∧
      receipt.inspection.reaction.surrounding = (nativeEvent admitted family native).2 := by
  rw [receipt.retainedReaction]
  exact ⟨rfl, rfl⟩

theorem reaction_affordable (receipt : Receipt admitted family rates native deliveryCost request budget) :
    reactionPrice admitted family rates native ≤ budget :=
  (native_paid_iff admitted family rates native budget).mp ⟨receipt.funding⟩

theorem complete_ledger (receipt : Receipt admitted family rates native deliveryCost request budget) :
    budget = receipt.remaining + receipt.spent := by
  have original := receipt.reaction_affordable
  have inspection := receipt.inspection.ledger
  dsimp only [remaining, spent]
  omega

theorem unfinished_is_quiet (receipt : Receipt admitted family rates native deliveryCost request budget)
    (unfinished : receipt.inspection.inspection.inspection.endpoint.pending ≠ []) :
    receipt.responses = 0 := receipt.inspection.unfinished_is_quiet unfinished

theorem inspect_responses
    (reactionAffordable : reactionPrice admitted family rates native ≤ budget)
    (offered : request.arrival = some (currentTarget admitted family native))
    (deliveryAffordable : deliveryCost request.question (currentTarget admitted family native) ≤
      budget - reactionPrice admitted family rates native) :
    (inspect reactionAffordable offered deliveryAffordable).responses =
      if reactionPrice admitted family rates native +
          deliveryCost request.question (currentTarget admitted family native) +
          (protocol admitted context deliveryCost).inspectionCost request.question
            (currentTarget admitted family native) ≤ budget then
        {(request.session, verdictOf ((protocol admitted context deliveryCost).test request.question
          (currentTarget admitted family native)), request.client, currentTarget admitted family native)}
      else 0 := by
  have packets := RhoScopedReactionAssayReceipts.Receipt.inspectTarget_responses
    (currentReaction admitted family native) offered deliveryAffordable
  change (RhoScopedReactionAssayReceipts.Receipt.inspectTarget
    (currentReaction admitted family native) offered deliveryAffordable).responses =
      if deliveryCost request.question (currentTarget admitted family native) +
          (protocol admitted context deliveryCost).inspectionCost request.question
            (currentTarget admitted family native) ≤
          budget - reactionPrice admitted family rates native then
        {(request.session, verdictOf ((protocol admitted context deliveryCost).test request.question
          (currentTarget admitted family native)), request.client, currentTarget admitted family native)}
      else 0 at packets
  change (RhoScopedReactionAssayReceipts.Receipt.inspectTarget
    (currentReaction admitted family native) offered deliveryAffordable).responses = _
  rw [packets]
  congr 1
  exact propext (by omega)

theorem current_target_certificate
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (response : Response (Process context) Clients) (reported : response ∈ receipt.responses) :
    ∃ answer : Bool, request.arrival = some (currentTarget admitted family native) ∧
      response = (request.session, verdictOf answer, request.client, currentTarget admitted family native) ∧
      StageCertificate admitted request.question (verdictOf answer) (currentTarget admitted family native) ∧
      receipt.spent = reactionPrice admitted family rates native +
        deliveryCost request.question (currentTarget admitted family native) +
        (protocol admitted context deliveryCost).inspectionCost request.question
          (currentTarget admitted family native) := by
  obtain ⟨answer, arrival, readout, certificate, cost, _affordable⟩ :=
    receipt.inspection.response_certificate response reported
  refine ⟨answer, arrival, readout, certificate, ?_⟩
  dsimp only [spent]
  rw [cost, Nat.add_assoc]

def revise {Hypotheses : Type*}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → Question context → Bool) (candidates : Finset Hypotheses) :
    Finset Hypotheses :=
  FiniteAssayLearner.revise prediction candidates request.question receipt.responses

theorem revision_readout {Hypotheses : Type*}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → Question context → Bool) (candidates : Finset Hypotheses)
    (hypothesis : Hypotheses) : hypothesis ∈ receipt.revise prediction candidates ↔
      hypothesis ∈ candidates ∧
        FiniteAssayLearner.Compatible prediction hypothesis request.question receipt.responses :=
  FiniteAssayLearner.revise_mem prediction candidates request.question receipt.responses hypothesis

theorem silence_preserves_candidates {Hypotheses : Type*}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → Question context → Bool) (candidates : Finset Hypotheses)
    (quiet : receipt.responses = 0) : receipt.revise prediction candidates = candidates := by
  unfold revise
  rw [quiet]
  exact FiniteAssayLearner.silence_preserves prediction candidates request.question

theorem removal_requires_actual_answer {Hypotheses : Type*}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → Question context → Bool) (candidates : Finset Hypotheses)
    (hypothesis : Hypotheses) (initial : hypothesis ∈ candidates) :
    hypothesis ∉ receipt.revise prediction candidates ↔
      ∃ response ∈ receipt.responses, prediction hypothesis request.question ≠ response.2.1.bit := by
  rw [revision_readout, and_iff_right initial]
  unfold FiniteAssayLearner.Compatible
  push Not
  rfl

end Receipt

end Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssays
