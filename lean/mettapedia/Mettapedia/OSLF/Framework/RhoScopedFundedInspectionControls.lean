import Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts
import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessorControls

/-!
# Actual scoped rho inspection prices and budget controls

The positive assay inspects the two reflection outcomes of an exposed
quotation. Its declared complete scan is affordable exactly at its earned
delivery-plus-inspection price. A smaller purse emits no answer. The negative
control confirms null's zeroth unfolding while refuting its continuing-reaction
hypothesis, separating paid approximation evidence from limit identification.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedFundedInspectionControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents RhoScopedFiniteSuccessors
open RhoScopedFiniteSuccessorControls RhoScopedDropSuccessors
open RhoScopedParallelReactiveSystem RhoScopedParallelInventory RhoScopedReactionReadout
open RhoScopedFundedInspection
open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

private theorem scan_top_sum {State : Type} (states : List State) :
    ((states.map (fun _ => (true, (1 : Nat)))).map Prod.snd).sum = states.length := by
  induction states with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

theorem complete_diamond_scan_price (admitted : SourceRule → Prop) {context : Ctx sig}
    (first label : Process context) :
    (inspect (presentation admitted context) (.diamond label .tt) rfl
      (FundedNuAssays.emptyEnvironment : BooleanEnv (Process context) 0) first).2 =
      1 + (successors admitted first label).card := by
  change 1 + (((successors admitted first label).toList.map (fun _ => (true, (1 : Nat)))).map
    Prod.snd).sum = _
  rw [scan_top_sum, Finset.length_toList]

def continuedReaction : PositiveHMLBody (Process []) :=
  ⟨.diamond (zero []) (.var 0), rfl, by decide⟩

def question : Question [] := (continuedReaction, 1)

def deliveryRate : Question [] → Process [] → Nat := fun _ _ => 1

def request : Request (Question []) (Process []) Nat Nat where
  question := question
  session := 21
  provider := 5
  client := 12
  arrival := some suspended

def paidRound (budget : Nat) := completedRound (protocol withReflection [] deliveryRate) request budget

theorem actual_two_outcome_inspection_price :
    (protocol withReflection [] deliveryRate).inspectionCost question suspended = 3 := by
  change (inspect (presentation withReflection []) (.diamond (zero []) .tt) rfl
    FundedNuAssays.emptyEnvironment suspended).2 = 3
  rw [complete_diamond_scan_price, visible_two_reflection_outcomes]

theorem actual_two_outcome_guard_confirms :
    (protocol withReflection [] deliveryRate).test question suspended = true := by
  change (inspect (presentation withReflection []) (.diamond (zero []) .tt) rfl
    FundedNuAssays.emptyEnvironment suspended).1 = true
  apply (inspection_truth withReflection (.diamond (zero []) .tt) rfl
    FundedNuAssays.emptyEnvironment suspended).mpr
  exact ⟨suspended, (mem_successors_iff withReflection _ _ _).mp
    (original_eta_self_outcome (quote visible)), trivial⟩

theorem exact_budget_emits_certificate :
    (paidRound 4).responses = {(21, Verdict.confirm, 12, suspended)} := by
  rw [paidRound, completedRound_responses]
  change AssayProbeDelivery.observed _ _ _ 21 5 12 (some suspended) 4 = _
  rw [AssayProbeDelivery.observed_some]
  change (if 1 + (protocol withReflection [] deliveryRate).inspectionCost question suspended ≤ 4 then
    {(21, verdictOf ((protocol withReflection [] deliveryRate).test question suspended), 12, suspended)}
    else 0) = _
  rw [actual_two_outcome_inspection_price, actual_two_outcome_guard_confirms]
  rfl

theorem insufficient_budget_emits_no_verdict : (paidRound 3).responses = 0 := by
  rw [paidRound, completedRound_responses]
  change AssayProbeDelivery.observed _ _ _ 21 5 12 (some suspended) 3 = _
  rw [AssayProbeDelivery.observed_some]
  change (if 1 + (protocol withReflection [] deliveryRate).inspectionCost question suspended ≤ 3 then
    {(21, verdictOf ((protocol withReflection [] deliveryRate).test question suspended), 12, suspended)}
    else 0) = _
  rw [actual_two_outcome_inspection_price]
  rfl

def actualSelfFiring : RhoScopedParallelReactiveSystem.Firing (rules := sourceRules)
    (admitted := withReflection) suspended (zero []) suspended where
  root := ⟨⟨.reflection, trivial⟩, RhoScopedInstanceReadout.reflection suspendedRaw
    RhoEquationConstructorControls.null⟩
  surrounding := zero []
  square := by
    change join suspended (zero []) = join (drop (quote suspended)) (zero [])
    rw [same_actual_name]
    rfl
  least := by rw [read_zero, Multiset.inter_zero]
  target := (join_zero_right suspended).symm

theorem offered_suspended : request.arrival = some suspended := rfl

theorem delivery_admitted (budget : Nat) (deliveryAffordable : 1 ≤ budget) :
    deliveryRate request.question suspended ≤ budget := deliveryAffordable

def instructionReceipt (budget : Nat) (deliveryAffordable : 1 ≤ budget) :=
  RhoScopedReactionAssayReceipts.Receipt.inspectTarget
    (deliveryCost := deliveryRate) (request := request) (budget := budget)
    actualSelfFiring offered_suspended (delivery_admitted budget deliveryAffordable)

theorem actual_firing_paid_instruction_packet :
    (instructionReceipt 4 (by decide)).responses = {(21, Verdict.confirm, 12, suspended)} := by
  rw [instructionReceipt, RhoScopedReactionAssayReceipts.Receipt.inspectTarget_responses]
  change (if 1 + (protocol withReflection [] deliveryRate).inspectionCost question suspended ≤ 4 then
    {(21, verdictOf ((protocol withReflection [] deliveryRate).test question suspended), 12, suspended)}
    else 0) = _
  rw [actual_two_outcome_inspection_price, actual_two_outcome_guard_confirms]
  rfl

theorem actual_firing_unfinished_inspection_quiet :
    (instructionReceipt 3 (by decide)).responses = 0 := by
  rw [instructionReceipt, RhoScopedReactionAssayReceipts.Receipt.inspectTarget_responses]
  change (if 1 + (protocol withReflection [] deliveryRate).inspectionCost question suspended ≤ 3 then
    {(21, verdictOf ((protocol withReflection [] deliveryRate).test question suspended), 12, suspended)}
    else 0) = _
  rw [actual_two_outcome_inspection_price]
  rfl

theorem actual_target_certificate : StageCertificate withReflection question .confirm suspended := by
  have present : (21, Verdict.confirm, 12, suspended) ∈
      (instructionReceipt 4 (by decide)).responses := by
    rw [actual_firing_paid_instruction_packet]
    exact Multiset.mem_singleton_self _
  obtain ⟨answer, _offered, printed, certificate, _cost, _affordable⟩ :=
    (instructionReceipt 4 (by decide)).response_certificate _ present
  have branch : Verdict.confirm = verdictOf answer :=
    (Prod.mk.inj (Prod.mk.inj printed).2).1
  rw [branch]
  exact certificate

theorem exact_budget_retains_real_paid_ledger : (paidRound 4).spent = 4 ∧ (paidRound 4).remaining = 0 := by
  have present : (21, Verdict.confirm, 12, suspended) ∈ (paidRound 4).responses := by
    rw [exact_budget_emits_certificate]
    exact Multiset.mem_singleton_self _
  obtain ⟨received, offered, _printed, _singleton, _affordable, spent⟩ :=
    (paidRound 4).response_sound _ present
  have same : received = suspended := Option.some.inj offered.symm
  rw [same] at spent
  change (paidRound 4).spent = 1 + (protocol withReflection [] deliveryRate).inspectionCost question suspended at spent
  rw [actual_two_outcome_inspection_price] at spent
  have ledger := (paidRound 4).ledger
  exact ⟨spent, by omega⟩

theorem null_initial_unfolding_confirmed :
    StageCertificate withReflection (continuedReaction, 0) .confirm (zero []) := trivial

theorem null_continuing_reaction_refuted :
    ¬ satisfies (originalLTS withReflection []) Env.empty (.nu continuedReaction.body) (zero []) := by
  rintro ⟨closed, contains, invariant⟩
  obtain ⟨next, transition, _preserved⟩ := invariant (zero []) contains
  have listed := (mem_successors_iff withReflection _ _ _).mpr transition
  rw [zero_identity_successors_empty] at listed
  exact Finset.notMem_empty next listed

theorem initial_confirmation_does_not_identify_limit :
    StageCertificate withReflection (continuedReaction, 0) .confirm (zero []) ∧
      ¬ satisfies (originalLTS withReflection []) Env.empty (.nu continuedReaction.body) (zero []) :=
  ⟨null_initial_unfolding_confirmed, null_continuing_reaction_refuted⟩

end Mettapedia.OSLF.Framework.RhoScopedFundedInspectionControls
