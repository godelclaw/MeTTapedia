import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessors
import Mettapedia.OSLF.Framework.FundedNuInstructionAssays
import Mettapedia.OSLF.Framework.FiniteAssayLearner

/-!
# Funded finite inspection of the original scoped rho reaction system

The actual original IPO relation is defined independently of the finite
successor presentation. Their earned comparison connects finite inspection,
unfolding certificates and actual paid protocol responses. Delivery rates
are supplied; inspection prices count the declared inspection instructions.
The resource protocol and its retained paths do not assert execution of an
inspection implementation inside rho or refinements to host work.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedFundedInspection

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents RhoScopedParallelContexts
open RhoScopedParallelReactiveSystem RhoScopedFiniteSuccessors
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.Logic.ModalMuCalculus
open Inspection Unfolding
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

def originalLTS (admitted : SourceRule → Prop) (context : Ctx sig) :
    LTS (Process context) (Process context) where
  trans first label second :=
    ActIPO (reactionRules sourceRules admitted) (arrow label) (arrow first) (arrow second)

def presentation (admitted : SourceRule → Prop) (context : Ctx sig) :
    SuccessorPresentation (Process context) (Process context) where
  successors first label := (RhoScopedFiniteSuccessors.successors admitted first label).toList

theorem listed_iff_actual (admitted : SourceRule → Prop) {context : Ctx sig}
    (first label second : Process context) :
    second ∈ (presentation admitted context).successors first label ↔
      (originalLTS admitted context).trans first label second := by
  rw [presentation, Finset.mem_toList]
  exact mem_successors_iff admitted first label second

theorem presentation_lts_eq_original (admitted : SourceRule → Prop) (context : Ctx sig) :
    (presentation admitted context).toLTS = originalLTS admitted context := by
  unfold SuccessorPresentation.toLTS originalLTS
  congr 1
  funext first label second
  exact propext (listed_iff_actual admitted first label second)

theorem inspection_truth (admitted : SourceRule → Prop) {context : Ctx sig} {slots : Nat}
    (formula : Formula (Process context) slots) (allowed : formula.isHML = true)
    (environment : BooleanEnv (Process context) slots) (first : Process context) :
    (inspect (presentation admitted context) formula allowed environment first).1 = true ↔
      satisfies (originalLTS admitted context) environment.toEnv formula first := by
  rw [← presentation_lts_eq_original]
  exact inspect_truth _ _ _ _ _

theorem inspection_falsehood (admitted : SourceRule → Prop) {context : Ctx sig} {slots : Nat}
    (formula : Formula (Process context) slots) (allowed : formula.isHML = true)
    (environment : BooleanEnv (Process context) slots) (first : Process context) :
    (inspect (presentation admitted context) formula allowed environment first).1 = false ↔
      ¬ satisfies (originalLTS admitted context) environment.toEnv formula first := by
  rw [← inspection_truth admitted formula allowed environment first]
  cases (inspect (presentation admitted context) formula allowed environment first).1 <;> decide

abbrev Question (context : Ctx sig) := FundedNuAssays.Question (Process context)

def protocol (admitted : SourceRule → Prop) (context : Ctx sig)
    (deliveryCost : Question context → Process context → Nat) :
    Protocol (Question context) (Process context) :=
  FundedNuAssays.protocol (presentation admitted context) deliveryCost

def StageCertificate (admitted : SourceRule → Prop) {context : Ctx sig}
    (question : Question context) (branch : Verdict) (first : Process context) : Prop :=
  match branch with
  | .confirm => satisfies (originalLTS admitted context) Env.empty
      (question.1.atStage question.2) first
  | .refute => ¬ satisfies (originalLTS admitted context) Env.empty
      (question.1.atStage question.2) first

theorem stage_certificate_comparison (admitted : SourceRule → Prop) {context : Ctx sig}
    (question : Question context) (branch : Verdict) (first : Process context) :
    FundedNuAssays.StageCertificate (presentation admitted context) question branch first ↔
      StageCertificate admitted question branch first := by
  cases branch <;> simp only [FundedNuAssays.StageCertificate, StageCertificate,
    presentation_lts_eq_original]

universe p c
variable {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _

/-- A public certificate and its purse ledger come from the supplied paid
path, and retain its received source-class state and complete request. -/
theorem paid_response_certificate (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat)
    {request : Request (Question context) (Process context) Providers Clients} {budget : Nat}
    (round : Round (protocol admitted context deliveryCost) request budget)
    (response : Response (Process context) Clients) (present : response ∈ round.responses) :
    ∃ first : Process context, request.arrival = some first ∧
      response = (request.session,
        verdictOf ((protocol admitted context deliveryCost).test request.question first),
        request.client, first) ∧
      StageCertificate admitted request.question
        (verdictOf ((protocol admitted context deliveryCost).test request.question first)) first ∧
      round.responses = {response} ∧
      round.spent = deliveryCost request.question first +
        (protocol admitted context deliveryCost).inspectionCost request.question first ∧
      round.spent ≤ budget := by
  obtain ⟨first, offered, printed, certificate, singleton, cost, affordable⟩ :=
    FundedNuAssays.response_certificate (presentation admitted context) deliveryCost round response present
  exact ⟨first, offered, printed,
    (stage_certificate_comparison admitted request.question _ first).mp certificate,
    singleton, cost, affordable⟩

/-- A finite refutation rejects the actual original greatest-fixed-point
hypothesis, including on its infinite scoped process carrier. -/
theorem paid_refutation (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat)
    {request : Request (Question context) (Process context) Providers Clients} {budget : Nat}
    (round : Round (protocol admitted context deliveryCost) request budget) (first : Process context)
    (present : (request.session, Verdict.refute, request.client, first) ∈ round.responses) :
    ¬ satisfies (originalLTS admitted context) Env.empty (.nu request.question.1.body) first := by
  rw [← presentation_lts_eq_original]
  exact FundedNuAssays.received_refutation _ deliveryCost round first present

/-- Finite paid evidence revises the declared version space by actual public
responses; it does not silently identify the full infinite-state hypothesis. -/
theorem learner_readout {Hypotheses : Type*} (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat)
    (prediction : Hypotheses → Question context → Bool)
    {budget : Nat} {requests : List (Request (Question context) (Process context) Providers Clients)}
    (campaign : Campaign (protocol admitted context deliveryCost) budget requests)
    (candidates : Finset Hypotheses) (hypothesis : Hypotheses) :
    hypothesis ∈ FiniteAssayLearner.learn prediction campaign candidates ↔ hypothesis ∈ candidates ∧
      ∀ packet ∈ campaign.publicLog, FiniteAssayLearner.Compatible prediction hypothesis packet.1 packet.2 :=
  FiniteAssayLearner.learn_mem prediction campaign candidates hypothesis

end Mettapedia.OSLF.Framework.RhoScopedFundedInspection
