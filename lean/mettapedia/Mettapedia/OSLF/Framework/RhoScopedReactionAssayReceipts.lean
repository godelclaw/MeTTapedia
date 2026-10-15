import Mettapedia.OSLF.Framework.RhoScopedFundedInspection

/-!
# Actual scoped rho firings with paid target-state evidence

Each receipt retains an original root, its least-label square and complete
surrounding process, together with a separately executed funded inspection
of that exact target class. Reporting produces a certificate about the
current reaction endpoint. Unfinished inspection produces no verdict.
The paid inspection is the declared resource machine, not a rho backend.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem
open Mettapedia.OSLF.Framework.RhoScopedFundedInspection
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay
open Mettapedia.Logic.ModalMuCalculus
open StackInspection

universe p c
variable {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _

structure Receipt (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat)
    (request : Request (Question context) (Process context) Providers Clients)
    (budget : Nat) (first label second : Process context) where
  reaction : RhoScopedParallelReactiveSystem.Firing (rules := sourceRules) (admitted := admitted)
    first label second
  inspection : FundedNuInstructionAssays.Receipt (presentation admitted context) deliveryCost request budget
  receivedTarget : inspection.received = second

namespace Receipt

variable {admitted : SourceRule → Prop} {context : Ctx sig}
variable {deliveryCost : Question context → Process context → Nat}
variable {request : Request (Question context) (Process context) Providers Clients}
variable {budget : Nat} {first label second : Process context}

/-- Construct the paid instruction prefix on the supplied reaction target.
The delivery admission is separate from inspection affordability. -/
def inspectTarget (reaction : RhoScopedParallelReactiveSystem.Firing
    (rules := sourceRules) (admitted := admitted) first label second)
    (offered : request.arrival = some second)
    (deliveryAffordable : deliveryCost request.question second ≤ budget) :
    Receipt admitted deliveryCost request budget first label second where
  reaction := reaction
  inspection := FundedNuInstructionAssays.inspectReceived (presentation admitted context)
    deliveryCost request budget second offered deliveryAffordable
  receivedTarget := rfl

def responses (receipt : Receipt admitted deliveryCost request budget first label second) :
    Multiset (Response (Process context) Clients) :=
  receipt.inspection.responses (presentation admitted context) deliveryCost

def remaining (receipt : Receipt admitted deliveryCost request budget first label second) : Nat :=
  receipt.inspection.remaining (presentation admitted context) deliveryCost

def spent (receipt : Receipt admitted deliveryCost request budget first label second) : Nat :=
  receipt.inspection.spent (presentation admitted context) deliveryCost

theorem inspectTarget_responses (reaction : RhoScopedParallelReactiveSystem.Firing
    (rules := sourceRules) (admitted := admitted) first label second)
    (offered : request.arrival = some second)
    (deliveryAffordable : deliveryCost request.question second ≤ budget) :
    (inspectTarget reaction offered deliveryAffordable).responses =
      if deliveryCost request.question second +
        (protocol admitted context deliveryCost).inspectionCost request.question second ≤ budget then
          {(request.session, verdictOf ((protocol admitted context deliveryCost).test request.question second),
            request.client, second)} else 0 :=
  FundedNuInstructionAssays.inspectReceived_responses (presentation admitted context)
    deliveryCost request budget second offered deliveryAffordable

theorem ledger (receipt : Receipt admitted deliveryCost request budget first label second) :
    budget = receipt.remaining + receipt.spent :=
  receipt.inspection.ledger (presentation admitted context) deliveryCost

theorem unfinished_is_quiet (receipt : Receipt admitted deliveryCost request budget first label second)
    (unfinished : receipt.inspection.inspection.endpoint.pending ≠ []) : receipt.responses = 0 :=
  receipt.inspection.unfinished_is_quiet (presentation admitted context) deliveryCost unfinished

/-- The certificate is attached to the actual reaction target, with the
original request and independently paid inspection ledger. -/
theorem response_certificate (receipt : Receipt admitted deliveryCost request budget first label second)
    (response : Response (Process context) Clients) (present : response ∈ receipt.responses) :
    ∃ answer : Bool, request.arrival = some second ∧
      response = (request.session, verdictOf answer, request.client, second) ∧
      StageCertificate admitted request.question (verdictOf answer) second ∧
      receipt.spent = deliveryCost request.question second +
        (protocol admitted context deliveryCost).inspectionCost request.question second ∧
      receipt.spent ≤ budget := by
  obtain ⟨answer, arrival, readout, certificate, cost, affordable⟩ :=
    receipt.inspection.response_certificate (presentation admitted context) deliveryCost response present
  rw [receipt.receivedTarget] at arrival readout certificate cost
  exact ⟨answer, arrival, readout,
    (stage_certificate_comparison admitted request.question _ second).mp certificate,
    cost, affordable⟩

theorem refuted_target (receipt : Receipt admitted deliveryCost request budget first label second)
    (reported : Funded.publicAnswer receipt.inspection.inspection.endpoint = some false) :
    ¬ satisfies (originalLTS admitted context) Env.empty (.nu request.question.1.body) second := by
  have refutation := receipt.inspection.received_refutation
    (presentation admitted context) deliveryCost reported
  rw [presentation_lts_eq_original, receipt.receivedTarget] at refutation
  exact refutation

end Receipt

/-- Both complementary guards inspect the same equation class. -/
def rawGuard (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat) (question : Question context)
    (process : Term sig context Srt.pr) : Bool :=
  (protocol admitted context deliveryCost).test question (project process)

theorem guard_equation_invariant (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat) (question : Question context)
    {first second : Term sig context Srt.pr} (same : EqClosure rhoSourceE first second) :
    rawGuard admitted deliveryCost question first = rawGuard admitted deliveryCost question second :=
  congrArg ((protocol admitted context deliveryCost).test question) (Quotient.sound same)

theorem complementary_guards_never_race (admitted : SourceRule → Prop) {context : Ctx sig}
    (deliveryCost : Question context → Process context → Nat) (question : Question context)
    {first second : Term sig context Srt.pr} (same : EqClosure rhoSourceE first second) :
    ¬ (rawGuard admitted deliveryCost question first = true ∧
      rawGuard admitted deliveryCost question second = false) := by
  rw [guard_equation_invariant admitted deliveryCost question same]
  rintro ⟨yes, no⟩
  exact Bool.noConfusion (yes.symm.trans no)

end Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts
