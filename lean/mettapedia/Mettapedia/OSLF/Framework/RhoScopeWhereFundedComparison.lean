import Mettapedia.OSLF.Framework.RhoScopeWhereNativeControls

/-!
# Paid response readouts compared with actual scoped rho receptions

For either independently checked specimen, every supplied paid response
has the same branch and name readout as the actual guarded rho execution.
Its session, requester, offered origin and exact purse ledger remain in
the resource protocol. Delivery and inspection are independent declared
prices. This comparison of readouts is not a state-by-state scheduler or
communication-cost refinement of the two operational systems.

An affordable completed controller supplies the single response. A delivered
but underfunded specimen supplies none, although the unpriced guarded rho
interpreter can still compute its semantic branch.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open Mettapedia.GSLT.Causality ResourceInteraction ProbeCampaign
open ComplementaryAssay (Verdict)
open Mettapedia.OSLF.MeTTaIL.FocusedRelationQueryExecution
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open ScopeWherePresentation ScopeWhereExecutionControls
open RhoGuardRelationQueries RhoScopeWhereNativeControls

noncomputable section

local instance nameDecision : DecidableEq (Name []) :=
  RhoIntrinsicReadback.equationClassDecision [] Srt.nm

local instance atomDecision : DecidablePred (atom.holds (Γ := [])) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

def specimen (sample : Verdict) : Name [] := quote (project (rawPayload sample))

def configured (delivery inspection : Name [] → Nat) : Protocol Unit (Name []) :=
  RhoScopeProbeRounds.protocol (fun _ : Unit => atom.holds) (fun _ : Unit => atom.holds)
    (fun _ => delivery) (fun _ => inspection)

def request (sample : Verdict) : Request Unit (Name []) Nat Nat :=
  ⟨Unit.unit, 0, 11, 22, some (specimen sample)⟩

theorem response_readout (delivery inspection : Name [] → Nat) (sample : Verdict)
    {budget : Nat} (round : Round (configured delivery inspection) (request sample) budget)
    (response : Response (Name []) Nat) (present : response ∈ round.responses) :
    response.2.1 = sample ∧ response.2.2.2 = specimen sample ∧
      response.1 = 0 ∧ response.2.2.1 = 22 ∧
      delivery (specimen sample) + inspection (specimen sample) ≤ budget ∧
      budget = round.remaining + delivery (specimen sample) + inspection (specimen sample) := by
  have account := RhoScopeProbeRounds.response_origin_and_account
    (fun _ : Unit => atom.holds) (fun _ : Unit => atom.holds)
    (fun _ => delivery) (fun _ => inspection) round response present
  have offered : some (specimen sample) = some response.2.2.2 := account.2.2.1
  have sameName : response.2.2.2 = specimen sample := (Option.some.inj offered).symm
  have sameBranch := RhoScopeProbeRounds.response_guard
    (fun _ : Unit => atom.holds) (fun _ : Unit => atom.holds)
    (fun _ => delivery) (fun _ => inspection) round response present
  rw [sameName] at sameBranch
  have selected : ComplementaryAssay.verdictOf (scopeTest (specimen sample)) = sample :=
    actual_choice sample
  have branch : response.2.1 = sample := sameBranch.trans selected
  rw [sameName] at account
  exact ⟨branch, sameName, account.1, account.2.1, account.2.2.2⟩

theorem response_agrees_with_actual_rho (delivery inspection : Name [] → Nat) (sample : Verdict)
    {budget : Nat} (round : Round (configured delivery inspection) (request sample) budget)
    (response : Response (Name []) Nat) (present : response ∈ round.responses) :
    rewriteAt (environment scopeTest) language 1 0 (source sample) =
      [(RuleHistory.fire (match response.2.1 with | .confirm => 2 | .refute => 3) [.root 0 0],
        target sample response.2.1)] ∧
      response.2.2.2 = specimen sample ∧
      budget = round.remaining + delivery response.2.2.2 + inspection response.2.2.2 := by
  obtain ⟨branch, value, _, _, _, account⟩ := response_readout delivery inspection sample round response present
  rw [branch, value]
  exact ⟨actual_single_rewrite sample, rfl, account⟩

def fiveTokenRound (sample : Verdict) (budget : Nat) :=
  completedRound (configured (fun _ => 2) (fun _ => 3)) (request sample) budget

theorem completed_response (sample : Verdict) :
    (fiveTokenRound sample 5).responses = {(0, sample, 22, specimen sample)} := by
  rw [fiveTokenRound, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  rw [if_pos (show (configured (fun _ => 2) (fun _ => 3)).deliveryCost Unit.unit (specimen sample) +
    (configured (fun _ => 2) (fun _ => 3)).inspectionCost Unit.unit (specimen sample) ≤ 5 by
      change 2 + 3 ≤ 5
      decide)]
  change {(0, ComplementaryAssay.verdictOf (scopeTest (specimen sample)), 22, specimen sample)} = _
  rw [show ComplementaryAssay.verdictOf (scopeTest (specimen sample)) = sample from actual_choice sample]

theorem underfunded_response_absent (sample : Verdict) :
    (fiveTokenRound sample 4).responses = 0 := by
  rw [fiveTokenRound, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  rw [if_neg (show ¬ (configured (fun _ => 2) (fun _ => 3)).deliveryCost Unit.unit (specimen sample) +
    (configured (fun _ => 2) (fun _ => 3)).inspectionCost Unit.unit (specimen sample) ≤ 4 by
      change ¬ 2 + 3 ≤ 4
      decide)]

end

end Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison
