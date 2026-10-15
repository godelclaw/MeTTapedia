import Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts
import Mettapedia.OSLF.Framework.RhoGroundedScopeGuardControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereErasureControls

/-!
# Actual positive and negative native scope receptions

The complete generated output-scope guard sends the two-output specimen
through the confirming receiver and quoted null through the refuting one.
Each firing retains the binder-dependent continuation and the exact
captured specimen. Its dependent receipt has least depth on confirmation
and genuine future exclusion on refutation. Erasing the guard admits the
opposite answer on these same specimens.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoScopeWhereNativeControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingConstructorPredicates BindingSubstitutionAlgebra
open RhoGuardRelationQueries
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching FocusedRelationQueryExecution
open ScopedPremiseExecution (RuleHistory StepOracle)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open ScopeWherePresentation ScopeWhereExecutionControls ScopeWhereErasureControls
open RhoEquationGeneratedScope RhoScopeAssayReceipts RhoGroundedScopeGuard
open RhoScopeDecisionControls
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)

noncomputable section

def atom : Predicate model Srt.pr := RhoSourceOutputPredicate.positive Srt.pr

local instance atomDecision (context : Ctx sig) : DecidablePred (atom.holds (Γ := context)) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

def scopeTest : Name [] → Bool := RhoScopeWhereNativeReceipts.scopeGuard atom atom

theorem actual_guard_answers (sample : Verdict) :
    scopeTest (quote (project (rawPayload sample))) = sample.bit := by
  cases sample with
  | confirm => exact future_name_accepted
  | refute =>
      apply (RhoGeneratedScopeDecision.guard_false_iff atom.holds atom.holds _).mpr
      exact RhoGeneratedScopeInventory.output_scope_excludes_null

theorem actual_choice (sample : Verdict) : chosenBranch scopeTest sample = sample := by
  apply Mettapedia.GSLT.Causality.ComplementaryAssay.verdict_eq_of_bit
  exact (Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf_bit _).trans (actual_guard_answers sample)

theorem actual_firing (sample : Verdict) :
    firing sample sample ∈ applyRuleWithOracle (rewriteAt (environment scopeTest) language 0)
      (environment scopeTest) language 0 (guardedComm sample) (source sample) := by
  rw [guarded_firings_exact]
  have permitted : enabled scopeTest sample (payload sample) = true :=
    (encoded_enabled_iff scopeTest sample (rawPayload sample)).mpr (actual_guard_answers sample)
  simp [permitted]

theorem actual_single_rewrite (sample : Verdict) :
    rewriteAt (environment scopeTest) language 1 0 (source sample) =
      [(.fire (match sample with | .confirm => 2 | .refute => 3) [.root 0 0], target sample sample)] := by
  rw [rewrite_one_exact, actual_choice]
  rfl

def receipt (sample : Verdict) :
    NativeDecisionReceipt atom atom (quote (project (rawPayload sample))) sample :=
  RhoScopeWhereNativeReceipts.nativeReceipt atom atom
    (rewriteAt (environment scopeTest) language 0) sample (source sample) (firing sample sample)
    ⟨[], 0, payload sample⟩ (rawPayload sample) (actual_firing sample)
    (captured_payload sample sample) (projected_payload sample)

theorem received_capture_retained (sample : Verdict) :
    (firing sample sample).completed = capture sample sample ∧
      lookup (firing sample sample).completed "p" = some ⟨[TypeExpr.name], 0, continuation sample⟩ ∧
      (firing sample sample).history = [.root 0 0] :=
  ⟨rfl, captured_continuation sample sample, rfl⟩

theorem confirmation_has_least_depth_zero :
    (positiveCertificate (receipt .confirm).observed).depth = 0 := by
  have least := positiveCertificate_least (receipt .confirm).observed futureCertificate
  have depth : futureCertificate.depth = 0 := rfl
  rw [depth] at least
  exact Nat.eq_zero_of_le_zero least

theorem refutation_excludes_every_future (future : Ctx sig)
    (env : Environment sig (TermQ rhoSourceE) [] future) :
    ¬ generated atom.holds atom.holds
      (model.substitution.substitute env (quote (zero []))) := (receipt .refute).sound future env

theorem negative_receipt_retains_origin (future : Ctx sig)
    (env : Environment sig (TermQ rhoSourceE) [] future) :
    (RhoGroundedScopeReceiptSubstitution.substitute env (receipt .refute)).origin.val = quote (zero []) := by
  rw [RhoGroundedScopeReceiptSubstitution.supplied_closed_origin_retained]
  rfl

theorem opposite_guarded_answer_absent (sample : Verdict) :
    applyRuleWithOracle (rewriteAt (environment scopeTest) language 0) (environment scopeTest) language 0
      (guardedComm (opposite sample)) (source sample) = [] := by
  rw [guarded_firings_exact]
  have rejected : enabled scopeTest (opposite sample) (payload sample) = false := by
    apply Bool.eq_false_iff.mpr
    intro admitted
    have contradictory := (encoded_enabled_iff scopeTest (opposite sample) (rawPayload sample)).mp admitted
    rw [actual_guard_answers] at contradictory
    cases sample <;> cases contradictory
  simp [rejected]

theorem erased_opposite_answer_reachable (sample : Verdict) :
    erasedTarget sample (opposite sample) ∈ ScopedRuleExecution.rewriteStepAt Engine.RelationEnv.empty
      Mettapedia.GSLT.Examples.ScopedRhoBinding.rhoCalcWithScopedSchemas 0 (erasedSource sample) :=
  either_erased_answer_reachable sample (opposite sample)

end

end Mettapedia.OSLF.Framework.RhoScopeWhereNativeControls
