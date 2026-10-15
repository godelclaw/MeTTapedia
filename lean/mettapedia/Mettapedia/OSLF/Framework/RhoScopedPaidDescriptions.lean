import Mettapedia.OSLF.Framework.PaidInterventionalDescriptions
import Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence
import Mettapedia.OSLF.Framework.RhoScopedFundedNativeAssayControls

/-!
# Partial descriptions of original rho native assays

Only actual completed responses contribute a feature to the description.
An answered receipt retains the original native event and paid reaction,
the delivered target and the independently executed instruction path.
The finite learner uses the same public answer projection, while the full
native certificate and complete occurrence ledger remain separate evidence.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedPaidDescriptions

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedDependentEventFutures RhoScopedNativeRateHistory RhoScopedFundedNativeAssays
open RhoScopedParallelInventory DisplayedPresheafTransport DisplayedPresheafComprehension
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay
open Mettapedia.CategoryTheory.PartialSections
open PaidInterventionalDescriptions

universe p c h

variable {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _
variable {context : Ctx sig}
variable {admitted : SourceRule → Prop}
variable {family : DisplayedFamily (RhoScopedEventPresheaf.terms .pr)}
variable {rates : SourceRule → Nat}
variable {native : NativeReceipt admitted family (context := context)}
variable {deliveryCost : RhoScopedFundedInspection.Question context → Process context → Nat}
variable {request : Request (RhoScopedFundedInspection.Question context) (Process context) Providers Clients}
variable {budget : Nat}

theorem response_consistent
    (receipt : Receipt admitted family rates native deliveryCost request budget) :
    ∀ first ∈ receipt.responses, ∀ second ∈ receipt.responses,
      first.2.1.bit = second.2.1.bit := by
  intro first inFirst second inSecond
  obtain ⟨firstAnswer, _, firstReadout, firstCertificate, _⟩ :=
    receipt.current_target_certificate first inFirst
  obtain ⟨secondAnswer, _, secondReadout, secondCertificate, _⟩ :=
    receipt.current_target_certificate second inSecond
  rw [firstReadout, secondReadout]
  change (verdictOf firstAnswer).bit = (verdictOf secondAnswer).bit
  rw [verdictOf_bit, verdictOf_bit]
  cases firstAnswer <;> cases secondAnswer <;>
    simp_all only [verdictOf, RhoScopedFundedInspection.StageCertificate]

def answer (receipt : Receipt admitted family rates native deliveryCost request budget) : Option Bool :=
  packetAnswer receipt.responses

theorem answer_none (receipt : Receipt admitted family rates native deliveryCost request budget) :
    answer receipt = none ↔ receipt.responses = 0 := packetAnswer_none _

theorem answer_some (receipt : Receipt admitted family rates native deliveryCost request budget)
    (value : Bool) :
    answer receipt = some value ↔
      ∃ response ∈ receipt.responses, response.2.1.bit = value :=
  packetAnswer_some receipt.responses (response_consistent receipt) value

/-- A single actual assay populates exactly its requested feature. -/
def answers (receipt : Receipt admitted family rates native deliveryCost request budget)
    (question : RhoScopedFundedInspection.Question context) : Option Bool := by
  classical
  exact if question = request.question then answer receipt else none

def describe (receipt : Receipt admitted family rates native deliveryCost request budget) :
    View (RhoScopedFundedInspection.Question context) Bool := viewOfAnswers (answers receipt)

theorem answers_requested (receipt : Receipt admitted family rates native deliveryCost request budget) :
    answers receipt request.question = answer receipt := by
  simp [answers]

theorem description_member (receipt : Receipt admitted family rates native deliveryCost request budget)
    (question : RhoScopedFundedInspection.Question context) :
    question ∈ (describe receipt).context ↔
      question = request.question ∧ ∃ response, response ∈ receipt.responses := by
  classical
  change (∃ value, answers receipt question = some value) ↔ _
  by_cases same : question = request.question
  · subst question
    rw [answers_requested]
    constructor
    · rintro ⟨value, reported⟩
      obtain ⟨response, authenticated, _⟩ := (answer_some receipt value).mp reported
      exact ⟨rfl, response, authenticated⟩
    · rintro ⟨_, response, authenticated⟩
      exact ⟨response.2.1.bit, (answer_some receipt _).mpr ⟨response, authenticated, rfl⟩⟩
  · simp [answers, same]

theorem unfinished_description_empty
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (unfinished : receipt.inspection.inspection.inspection.endpoint.pending ≠ []) :
    (describe receipt).context = ∅ := by
  have quiet := receipt.unfinished_is_quiet unfinished
  ext question
  rw [description_member]
  simp [quiet]

theorem quiet_description_empty
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (quiet : receipt.responses = 0) : (describe receipt).context = ∅ := by
  ext question
  rw [description_member]
  simp [quiet]

/-- Complete receipt fibres retain the real rho reaction and instruction
execution; no probe execution is substituted for these machines. -/
structure AnsweredReceipt (admitted : SourceRule → Prop)
    (family : DisplayedFamily (RhoScopedEventPresheaf.terms .pr)) (rates : SourceRule → Nat)
    (native : NativeReceipt admitted family (context := context))
    (deliveryCost : RhoScopedFundedInspection.Question context → Process context → Nat)
    (request : Request (RhoScopedFundedInspection.Question context) (Process context) Providers Clients)
    (budget : Nat) (readout : Bool) where
  actual : Receipt admitted family rates native deliveryCost request budget
  response : Response (Process context) Clients
  authenticated : response ∈ actual.responses
  bit : response.2.1.bit = readout

namespace AnsweredReceipt

variable {readout : Bool}

theorem actual_answer
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    answer receipt.actual = some readout :=
  (answer_some _ _).mpr ⟨receipt.response, receipt.authenticated, receipt.bit⟩

theorem requested_feature
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    request.question ∈ (describe receipt.actual).context :=
  ⟨readout, (answers_requested receipt.actual).trans receipt.actual_answer⟩

theorem description_readout
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    (describe receipt.actual).values ⟨request.question, receipt.requested_feature⟩ = readout :=
  viewOfAnswers_readout (answers receipt.actual) request.question readout
    ((answers_requested receipt.actual).trans receipt.actual_answer)

theorem current_target_certificate
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    RhoScopedFundedInspection.StageCertificate admitted request.question (verdictOf readout)
      (currentTarget admitted family native) := by
  obtain ⟨value, _, response, certificate, _⟩ :=
    receipt.actual.current_target_certificate receipt.response receipt.authenticated
  have valueReadout : value = readout := by
    have bit := receipt.bit
    rw [response] at bit
    simpa only [verdictOf_bit] using bit
  rw [valueReadout] at certificate
  exact certificate

theorem exact_combined_ledger
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    budget = receipt.actual.remaining +
      (reactionPrice admitted family rates native +
        deliveryCost request.question (currentTarget admitted family native) +
        (RhoScopedFundedInspection.protocol admitted context deliveryCost).inspectionCost
          request.question (currentTarget admitted family native)) := by
  obtain ⟨_, _, _, _, spent⟩ :=
    receipt.actual.current_target_certificate receipt.response receipt.authenticated
  rw [← spent]
  exact receipt.actual.complete_ledger

theorem original_event_word
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    receipt.actual.funding.eventWord = [nativeOccurrence admitted family native] :=
  native_paid_word admitted family rates native budget receipt.actual.funding

theorem original_firing
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout) :
    receipt.actual.inspection.reaction = currentReaction admitted family native :=
  receipt.actual.retainedReaction

end AnsweredReceipt

theorem compatible_iff_partial_answer {Hypotheses : Type h}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → RhoScopedFundedInspection.Question context → Bool)
    (hypothesis : Hypotheses) :
    FiniteAssayLearner.Compatible prediction hypothesis request.question receipt.responses ↔
      ∀ value, answer receipt = some value → prediction hypothesis request.question = value := by
  constructor
  · intro compatible value reported
    obtain ⟨response, authenticated, bit⟩ := (answer_some receipt value).mp reported
    exact (compatible response authenticated).trans bit
  · intro compatible response authenticated
    exact compatible response.2.1.bit
      ((answer_some receipt _).mpr ⟨response, authenticated, rfl⟩)

/-- The finite update and the partial description expose the same learner
contract; silence supplies no additional feature and removes no candidate. -/
theorem revision_description_readout {Hypotheses : Type h}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → RhoScopedFundedInspection.Question context → Bool)
    (candidates : Finset Hypotheses) (hypothesis : Hypotheses) :
    hypothesis ∈ receipt.revise prediction candidates ↔ hypothesis ∈ candidates ∧
      ∀ feature (present : feature ∈ (describe receipt).context),
        prediction hypothesis feature = (describe receipt).values ⟨feature, present⟩ := by
  rw [Receipt.revision_readout, compatible_iff_partial_answer]
  apply and_congr_right'
  constructor
  · intro compatible feature present
    have requested := ((description_member receipt feature).mp present).1
    subst feature
    exact compatible _ ((answers_requested receipt).symm.trans
      (viewOfAnswers_value (answers receipt) request.question present))
  · intro compatible value reported
    have present : request.question ∈ (describe receipt).context :=
      ⟨value, (answers_requested receipt).trans reported⟩
    exact (compatible request.question present).trans
      (viewOfAnswers_readout (answers receipt) request.question value
        ((answers_requested receipt).trans reported))

theorem silence_preserves_learning {Hypotheses : Type h}
    (receipt : Receipt admitted family rates native deliveryCost request budget)
    (prediction : Hypotheses → RhoScopedFundedInspection.Question context → Bool)
    (candidates : Finset Hypotheses) (quiet : answer receipt = none) :
    receipt.revise prediction candidates = candidates :=
  receipt.silence_preserves_candidates prediction candidates ((answer_none receipt).mp quiet)

theorem completed_refutation_removes {Hypotheses : Type h} {readout : Bool}
    (receipt : AnsweredReceipt admitted family rates native deliveryCost request budget readout)
    (prediction : Hypotheses → RhoScopedFundedInspection.Question context → Bool)
    (candidates : Finset Hypotheses) (hypothesis : Hypotheses)
    (contradiction : prediction hypothesis request.question ≠ readout) :
    hypothesis ∉ receipt.actual.revise prediction candidates := by
  apply FiniteAssayLearner.response_removes prediction candidates request.question
    receipt.actual.responses hypothesis receipt.response receipt.authenticated
  rw [receipt.bit]
  exact contradiction

namespace Controls

open RhoScopedFundedNativeAssayControls

def completed : AnsweredReceipt withReflection quotedTargetOrigins
    RhoScopedNativeRateHistoryControls.rates RhoScopedFundedNativeAssayControls.native RhoScopedFundedInspectionControls.deliveryRate
    RhoScopedFundedInspectionControls.request 9 true where
  actual := assay 9 (by decide) (by decide)
  response := (21, Verdict.confirm, 12, suspended)
  authenticated := by
    rw [complete_price_emits_target_certificate]
    exact Multiset.mem_singleton_self _
  bit := rfl

def incomplete := assay 8 (by decide) (by decide)

theorem complete_description_answer : answer completed.actual = some true := completed.actual_answer

theorem complete_description_context :
    (describe completed.actual).context = {RhoScopedFundedInspectionControls.question} := by
  ext question
  rw [description_member]
  have supplied : ∃ response, response ∈ completed.actual.responses :=
    ⟨completed.response, completed.authenticated⟩
  simp only [supplied, and_true, Set.mem_singleton_iff]
  rfl

theorem complete_description_native_certificate :
    RhoScopedFundedInspection.StageCertificate withReflection RhoScopedFundedInspectionControls.question
      Verdict.confirm suspended := by
  have certificate := completed.current_target_certificate
  rw [exact_target] at certificate
  exact certificate

theorem complete_description_exact_ledger :
    completed.actual.spent = 9 ∧ completed.actual.remaining = 0 ∧
      9 = completed.actual.remaining + completed.actual.spent :=
  ⟨complete_answer_price_and_balance.1, complete_answer_price_and_balance.2,
    completed.actual.complete_ledger⟩

theorem complete_description_original_occurrence :
    completed.actual.funding.eventWord = [nativeOccurrence withReflection quotedTargetOrigins RhoScopedFundedNativeAssayControls.native] :=
  completed.original_event_word

theorem complete_description_revises :
    completed.actual.revise predictions {false, true} = {true} := by
  ext hypothesis
  rw [revision_description_readout]
  constructor
  · rintro ⟨initial, agrees⟩
    have actual := agrees _ completed.requested_feature
    rw [completed.description_readout] at actual
    exact Finset.mem_singleton.mpr actual
  · intro retained
    have same : hypothesis = true := Finset.mem_singleton.mp retained
    subst hypothesis
    refine ⟨by simp, ?_⟩
    intro feature present
    have requested := ((description_member completed.actual feature).mp present).1
    subst feature
    exact completed.description_readout.symm

theorem correct_hypothesis_survives :
    true ∈ completed.actual.revise predictions {false, true} := by
  rw [complete_description_revises]
  exact Finset.mem_singleton_self _

theorem incorrect_hypothesis_refuted :
    false ∉ completed.actual.revise predictions {false, true} :=
  completed_refutation_removes completed predictions {false, true} false (by decide)

theorem one_unit_short_has_no_description :
    answer incomplete = none ∧ (describe incomplete).context = ∅ :=
  ⟨(answer_none incomplete).mpr incomplete_price_emits_no_verdict,
    quiet_description_empty incomplete incomplete_price_emits_no_verdict⟩

theorem one_unit_short_keeps_candidates :
    incomplete.revise predictions {false, true} = {false, true} :=
  silence_preserves_learning incomplete predictions {false, true}
    one_unit_short_has_no_description.1

theorem one_unit_short_retains_reaction :
    incomplete.funding.eventWord = [nativeOccurrence withReflection quotedTargetOrigins RhoScopedFundedNativeAssayControls.native] :=
  short_budget_still_retains_funded_reaction

end Controls

namespace Native

/-- The original native state and supplied request are retained in the
public index; the intervention is the admitted identity-labelled reaction. -/
abbrev Index := PaidInterventionalNativeEvidence.Key
  (NativeReceipt withReflection quotedTargetOrigins (context := []))
  (Process []) (RhoScopedFundedInspection.Question []) (Process []) Nat Nat

/-- The fibre contains the actual original reaction funding and modal
instruction receipt. The label admission is separate from its Boolean answer. -/
structure Evidence (key : Index) where
  budget : Nat
  actual : AnsweredReceipt withReflection quotedTargetOrigins
    RhoScopedNativeRateHistoryControls.rates key.snapshot
    RhoScopedFundedInspectionControls.deliveryRate key.request budget key.answer
  identityLabel : key.intervention = zero []

def initial (key : Index) (evidence : Evidence key) : Nat := evidence.budget

def receiptFamily : DisplayedFamily ((Functor.const
    PaidInterventionalNativeEvidence.BudgetWorldᵒᵖ).obj Index) :=
  PaidInterventionalNativeEvidence.fundedFamily Evidence initial

def comprehension : PaidInterventionalNativeEvidence.BudgetWorldᵒᵖ ⥤ Type :=
  PaidInterventionalNativeEvidence.fundedComprehension Evidence initial

def answerFamily : DisplayedFamily PaidInterventionalNativeEvidence.answerBase :=
  PaidInterventionalNativeEvidence.answerReceipts Evidence initial (fun key => key.answer)

def receiptBudgetArrow (first second : Nat) (included : first ≤ second) (key : Index) :=
  CategoryOfElements.homMk
    (F := (Functor.const PaidInterventionalNativeEvidence.BudgetWorldᵒᵖ).obj Index)
    ⟨Opposite.op first, key⟩ ⟨Opposite.op second, key⟩
    (homOfLE (X := PaidInterventionalNativeEvidence.BudgetWorld) included).op rfl

theorem receipt_family_substitution (first second : Nat) (included : first ≤ second)
    (key : Index) (evidence : Evidence key) (affordable : initial key evidence ≤ first) :
    receiptFamily.map (receiptBudgetArrow first second included key)
      (PaidInterventionalNativeEvidence.introduce Evidence initial first key evidence affordable) =
      PaidInterventionalNativeEvidence.introduce Evidence initial second key evidence
        (affordable.trans included) :=
  PaidInterventionalNativeEvidence.introduced_substitution
    Evidence initial first second included key evidence affordable

def answerBudgetArrow (first second : Nat) (included : first ≤ second) (bit : Bool) :=
  CategoryOfElements.homMk (F := PaidInterventionalNativeEvidence.answerBase)
    ⟨Opposite.op first, bit⟩ ⟨Opposite.op second, bit⟩
    (homOfLE (X := PaidInterventionalNativeEvidence.BudgetWorld) included).op rfl

def widenAnswer {first second : Nat} (included : first ≤ second) {bit : Bool}
    (receipt : answerFamily.obj ⟨Opposite.op first, bit⟩) :
    answerFamily.obj ⟨Opposite.op second, bit⟩ :=
  answerFamily.map (answerBudgetArrow first second included bit) receipt

theorem widenAnswer_retains_witness {first second : Nat} (included : first ≤ second) {bit : Bool}
    (receipt : answerFamily.obj ⟨Opposite.op first, bit⟩) :
    (widenAnswer included receipt).val.2.val.val = receipt.val.2.val.val := rfl

theorem widenAnswer_identity {allowance : Nat} {bit : Bool}
    (receipt : answerFamily.obj ⟨Opposite.op allowance, bit⟩) :
    widenAnswer le_rfl receipt = receipt := by
  change answerFamily.map (𝟙 _) receipt = receipt
  exact answerFamily.map_id_apply _ receipt

theorem widenAnswer_composition {first second third : Nat}
    (earlier : first ≤ second) (later : second ≤ third) {bit : Bool}
    (receipt : answerFamily.obj ⟨Opposite.op first, bit⟩) :
    widenAnswer later (widenAnswer earlier receipt) =
      widenAnswer (earlier.trans later) receipt := by
  change answerFamily.map (answerBudgetArrow second third later bit)
    (answerFamily.map (answerBudgetArrow first second earlier bit) receipt) =
      answerFamily.map ((answerBudgetArrow first second earlier bit) ≫
        (answerBudgetArrow second third later bit)) receipt
  exact (answerFamily.map_comp_apply _ _ receipt).symm

def completedKey : Index where
  snapshot := RhoScopedFundedNativeAssayControls.native
  intervention := zero []
  request := RhoScopedFundedInspectionControls.request
  answer := true

def completedEvidence : Evidence completedKey where
  budget := 9
  actual := Controls.completed
  identityLabel := rfl

def answered (allowance : Nat) (affordable : 9 ≤ allowance) :
    answerFamily.obj ⟨Opposite.op allowance, true⟩ :=
  PaidInterventionalNativeEvidence.retainAnswer Evidence initial (fun key => key.answer)
    allowance completedKey completedEvidence affordable

theorem answer_family_retains_complete_receipt (allowance : Nat) (affordable : 9 ≤ allowance) :
    (answered allowance affordable).val.2.val.val =
      (⟨completedKey, completedEvidence⟩ : Sigma Evidence) :=
  PaidInterventionalNativeEvidence.answer_retains_witness Evidence initial (fun key => key.answer)
    allowance completedKey completedEvidence affordable

theorem answer_family_original_occurrence (allowance : Nat) (affordable : 9 ≤ allowance) :
    (answered allowance affordable).val.2.val.val.2.actual.actual.funding.eventWord =
      [nativeOccurrence withReflection quotedTargetOrigins RhoScopedFundedNativeAssayControls.native] := by
  rw [answer_family_retains_complete_receipt]
  exact Controls.complete_description_original_occurrence

theorem answer_family_current_certificate (allowance : Nat) (affordable : 9 ≤ allowance) :
    RhoScopedFundedInspection.StageCertificate withReflection
      (answered allowance affordable).val.2.val.val.1.request.question
      (verdictOf (answered allowance affordable).val.2.val.val.1.answer)
      (currentTarget withReflection quotedTargetOrigins
        (answered allowance affordable).val.2.val.val.1.snapshot) := by
  rw [answer_family_retains_complete_receipt]
  exact completedEvidence.actual.current_target_certificate

theorem answer_family_ledger (allowance : Nat) (affordable : 9 ≤ allowance) :
    (answered allowance affordable).val.2.val.val.2.budget =
      (answered allowance affordable).val.2.val.val.2.actual.actual.remaining +
      (answered allowance affordable).val.2.val.val.2.actual.actual.spent := by
  rw [answer_family_retains_complete_receipt]
  exact completedEvidence.actual.actual.complete_ledger

theorem widened_answer_current_certificate {first second : Nat} (included : first ≤ second)
    (affordable : 9 ≤ first) :
    RhoScopedFundedInspection.StageCertificate withReflection
      (widenAnswer included (answered first affordable)).val.2.val.val.1.request.question
      (verdictOf (widenAnswer included (answered first affordable)).val.2.val.val.1.answer)
      (currentTarget withReflection quotedTargetOrigins
        (widenAnswer included (answered first affordable)).val.2.val.val.1.snapshot) := by
  rw [widenAnswer_retains_witness]
  exact answer_family_current_certificate first affordable

end Native

end Mettapedia.OSLF.Framework.RhoScopedPaidDescriptions
