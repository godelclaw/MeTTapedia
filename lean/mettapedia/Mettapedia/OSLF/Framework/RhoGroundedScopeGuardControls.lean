import Mettapedia.OSLF.Framework.RhoGroundedScopeProbeReceipts
import Mettapedia.OSLF.Framework.RhoScopeAssayFutureControls

/-!
# Grounded native guards and the open-variable separator

The actual output scope admits a two-output name and excludes quoted null.
Its generic open variable satisfies neither the scope nor native negation,
and no Boolean map natural on every open term can classify it. On retained
closed origins both native guards have the correct, complementary answers.

The paid control really delivers quoted null and fires its negative
receiver. The resulting receipt excludes scope certificates at every future
substitution. A supplied positive receipt retains its origin, least depth
and ordered premises. An underfunded delivered specimen still yields no
verdict.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoGroundedScopeGuardControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open BindingGroundedPredicates BindingPredicateFutureLogic BindingPredicateBooleanGuard
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeInventory
open RhoScopeDecisionControls RhoScopeAssayReceipts RhoGroundedScopeGuard
open Mettapedia.GSLT.Causality ResourceInteraction ProbeCampaign
open ComplementaryAssay (Verdict)

noncomputable section

local instance nameClassDecision (context : Ctx sig) : DecidableEq (Name context) :=
  RhoIntrinsicReadback.equationClassDecision context Srt.nm

local instance atomDecision (context : Ctx sig) :
    DecidablePred ((RhoSourceOutputPredicate.positive Srt.pr).holds (Γ := context)) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

local instance scopeDecision (context : Ctx sig) : DecidablePred (outputScope.holds (Γ := context)) :=
  fun name => RhoGeneratedScopeDecision.generatedDecision
    (RhoSourceOutputPredicate.positive Srt.pr).holds
    (RhoSourceOutputPredicate.positive Srt.pr).holds name

def excludedName : Name [] := quote (zero [])

theorem admitted_member : outputScope.holds futureName := certificate_sound futureCertificate

theorem excluded_member : ¬ outputScope.holds excludedName := output_scope_excludes_null

theorem open_native_guards_do_not_cover :
    ¬ outputScope.holds (genericVariable (A := model)) ∧
      ¬ (nativeNegation outputScope).holds (genericVariable (A := model)) :=
  generic_variable_has_neither outputScope futureName excludedName admitted_member excluded_member

theorem no_unrestricted_boolean_classifier :
    ¬ ∃ readout : semanticPrograms model Srt.nm ⟶ booleans (A := model),
      ∀ {context : Ctx sig} (value : Name context),
        (readout.app (Opposite.op
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
            model.substitution.toClone context)) value).down = decision outputScope value :=
  no_calibrated_boolean_transformation outputScope futureName excludedName admitted_member excluded_member

theorem grounded_negative_survives_every_future (context : Ctx sig) :
    (negative (RhoSourceOutputPredicate.positive Srt.pr)
      (RhoSourceOutputPredicate.positive Srt.pr)).holds (ground (A := model) context excludedName) :=
  (grounded_negation _ _ context excludedName).mpr excluded_member

theorem classifier_has_two_distinct_answers (world : Base model) :
    ((classifier (RhoSourceOutputPredicate.positive Srt.pr)
      (RhoSourceOutputPredicate.positive Srt.pr)).app world futureName).down = true ∧
    ((classifier (RhoSourceOutputPredicate.positive Srt.pr)
      (RhoSourceOutputPredicate.positive Srt.pr)).app world excludedName).down = false := by
  exact ⟨(BindingClosedPredicateGuard.guard_true outputScope futureName world).mpr admitted_member,
    (BindingClosedPredicateGuard.guard_false outputScope excludedName world).mpr excluded_member⟩

def positiveReceipt : NativeDecisionReceipt
    (RhoSourceOutputPredicate.positive Srt.pr) (RhoSourceOutputPredicate.positive Srt.pr)
    futureName .confirm :=
  promote _ _ RhoScopeAssayFutureControls.futureReceipt
    ⟨futureName, ground_empty (A := model) futureName⟩

theorem positive_future_origin_and_depth {context : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) [] context) :
    (RhoGroundedScopeReceiptSubstitution.substitute env positiveReceipt).origin.val = futureName ∧
      (positiveCertificate
        (RhoGroundedScopeReceiptSubstitution.substitute env positiveReceipt).observed).depth = 0 := by
  refine ⟨RhoGroundedScopeReceiptSubstitution.supplied_closed_origin_retained env positiveReceipt, ?_⟩
  rw [RhoGroundedScopeReceiptSubstitution.confirmation_depth_retained]
  have least := positiveCertificate_least positiveReceipt.observed futureCertificate
  have depth : futureCertificate.depth = 0 := rfl
  rw [depth] at least
  exact Nat.eq_zero_of_le_zero least

def questions (_ : Unit) : Predicate model Srt.pr :=
  RhoSourceOutputPredicate.positive Srt.pr

local instance questionDecision : ∀ question : Unit, ∀ context : Ctx sig,
    DecidablePred ((questions question).holds (Γ := context)) :=
  fun _ context => atomDecision context

def protocol : Protocol Unit (Name []) :=
  RhoScopeProbeRounds.protocol (fun q => (questions q).holds) (fun q => (questions q).holds)
    (fun _ _ => 2) (fun _ _ => 3)

def request (arrival : Option (Name [])) : Request Unit (Name []) Nat Nat :=
  ⟨Unit.unit, 0, 11, 22, arrival⟩

def run (name : Name []) (budget : Nat) :=
  completedRound protocol (request (some name)) budget

theorem paid_negative_response :
    (run excludedName 5).responses = {(0, Verdict.refute, 22, excludedName)} := by
  rw [run, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  rw [if_pos (show protocol.deliveryCost Unit.unit excludedName +
    protocol.inspectionCost Unit.unit excludedName ≤ 5 by decide)]
  change {(0, ComplementaryAssay.verdictOf
    (RhoGeneratedScopeDecision.guard (questions Unit.unit).holds (questions Unit.unit).holds excludedName),
    22, excludedName)} = _
  rw [(RhoGeneratedScopeDecision.guard_false_iff
    (questions Unit.unit).holds (questions Unit.unit).holds excludedName).mpr excluded_member]
  rfl

theorem paid_negative_present :
    (0, Verdict.refute, 22, excludedName) ∈ (run excludedName 5).responses := by
  rw [paid_negative_response]
  exact Multiset.mem_singleton_self _

def negativeReceipt : NativeDecisionReceipt (questions Unit.unit) (questions Unit.unit)
    excludedName .refute :=
  RhoGroundedScopeProbeReceipts.responseReceipt questions questions (fun _ _ => 2) (fun _ _ => 3)
    (run excludedName 5) (0, Verdict.refute, 22, excludedName) paid_negative_present
    ⟨excludedName, ground_empty (A := model) excludedName⟩

theorem actual_paid_negative_is_native (future : Ctx sig)
    (env : Environment sig (TermQ rhoSourceE) [] future) :
    ¬ generated (questions Unit.unit).holds (questions Unit.unit).holds
      (model.substitution.substitute env excludedName) :=
  negativeReceipt.sound future env

theorem underfunded_grounded_positive_yields_no_verdict :
    outputScope.holds futureName ∧ (run futureName 4).responses = 0 := by
  refine ⟨admitted_member, ?_⟩
  rw [run, completedRound_responses]
  dsimp only [request]
  rw [AssayProbeDelivery.observed_some]
  change (if 2 + 3 ≤ 4 then _ else 0) = 0
  exact if_neg (by decide)

end

end Mettapedia.OSLF.Framework.RhoGroundedScopeGuardControls
