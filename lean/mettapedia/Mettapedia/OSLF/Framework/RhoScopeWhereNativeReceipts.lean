import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereQueryExecution
import Mettapedia.OSLF.Framework.RhoGroundedScopeReceiptSubstitution

/-!
# Native dependent certificates recovered from actual guarded rho firings

The relation interpreter applies the complete scope decision to the class
of the actual captured closed payload. A successful rule firing earns its
branch certificate, complete contextual capture and selected query row.
The retained closed origin licenses genuine future negation on refutation.
The returned dereference quotes to the same name by the source eta equation.

The supplied payload and its projection are an admission comparison with
the firing's captured value. Neither a guard answer nor a scope witness is
assumed. This interpreter join does not run the scope search in a native VM.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoGuardRelationQueries
open BindingConstructorPredicates BindingSubstitutionAlgebra BindingGroundedPredicates
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching FocusedRelationQueryExecution
open ScopedPremiseExecution (StepOracle RuleFiring PremiseEvent)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open ScopeWherePresentation ScopeWhereQueryExecution
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoScopeAssayReceipts RhoGroundedScopeGuard
open Mettapedia.GSLT.Causality.ComplementaryAssay

noncomputable section

variable (left right : Predicate model Srt.pr)
variable [∀ context : Ctx sig, DecidablePred (left.holds (Γ := context))]
variable [∀ context : Ctx sig, DecidablePred (right.holds (Γ := context))]

def scopeGuard : Name [] → Bool := RhoGeneratedScopeDecision.guard left.holds right.holds

theorem firing_guard_value {Evidence : Type} (oracle : StepOracle Evidence)
    (branch : Verdict) (source : Pattern) (firing : RuleFiring Evidence)
    (value : ContextualValue) (payload : Term sig [] Srt.pr)
    (present : firing ∈ applyRuleWithOracle oracle (environment (scopeGuard left right)) language 0
      (guardedComm branch) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some (encodeTerm payload)) :
    scopeGuard left right (quote (project payload)) = branch.bit :=
  (encoded_enabled_iff (scopeGuard left right) branch payload).mp
    (firing_query_readout (scopeGuard left right) oracle branch source firing value
      (encodeTerm payload) present found reading).1

def nativeReceipt {Evidence : Type} (oracle : StepOracle Evidence)
    (branch : Verdict) (source : Pattern) (firing : RuleFiring Evidence)
    (value : ContextualValue) (payload : Term sig [] Srt.pr)
    (present : firing ∈ applyRuleWithOracle oracle (environment (scopeGuard left right)) language 0
      (guardedComm branch) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some (encodeTerm payload)) :
    NativeDecisionReceipt left right (quote (project payload)) branch := by
  have actualBit := firing_guard_value left right oracle branch source firing value payload present found reading
  have actualBranch : verdictOf (scopeGuard left right (quote (project payload))) = branch :=
    verdict_eq_of_bit ((verdictOf_bit _).trans actualBit)
  have receipt : DecisionReceipt left.holds right.holds (quote (project payload)) branch :=
    actualBranch ▸ decisionReceipt left.holds right.holds (quote (project payload))
  exact promote left right receipt
    ⟨quote (project payload), ground_empty (A := model) (quote (project payload))⟩

theorem retained_capture_and_history {Evidence : Type} (oracle : StepOracle Evidence)
    (branch : Verdict) (source : Pattern) (firing : RuleFiring Evidence)
    (value : ContextualValue) (payload : Term sig [] Srt.pr)
    (present : firing ∈ applyRuleWithOracle oracle (environment (scopeGuard left right)) language 0
      (guardedComm branch) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some (encodeTerm payload)) :
    firing.completed = firing.captured ∧ firing.history = [.root 0 0] :=
  (firing_query_readout (scopeGuard left right) oracle branch source firing value
    (encodeTerm payload) present found reading).2

theorem returned_quote_is_tested_name (payload : Term sig [] Srt.pr) :
    quote (drop (quote (project payload))) = quote (project payload) := quote_drop _

/-- Read the actual dereferenced output payload emitted by the bound
continuation. Its quotation is the name whose guard was executed. -/
theorem returned_payload_readback (payload : Term sig [] Srt.pr) :
    (RhoIntrinsicReadback.readProcessClass []
      (.apply "PDrop" [.apply "NQuote" [encodeTerm payload]])).map quote =
        some (quote (project payload)) := by
  obtain ⟨decoded, reading, represented⟩ := RhoIntrinsicReadback.read_encoded_class payload
  change RhoIntrinsicReadback.readProcess [] (encodeTerm payload) = some decoded at reading
  rw [RhoIntrinsicReadback.readProcessClass_drop, RhoIntrinsicReadback.readNameClass_quote]
  simp only [RhoIntrinsicReadback.readProcessClass, reading, Option.map_some,
    represented, quote_drop]

theorem confirmed_certificate_least {Evidence : Type} (oracle : StepOracle Evidence)
    (source : Pattern) (firing : RuleFiring Evidence) (value : ContextualValue)
    (payload : Term sig [] Srt.pr)
    (present : firing ∈ applyRuleWithOracle oracle (environment (scopeGuard left right)) language 0
      (guardedComm .confirm) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some (encodeTerm payload))
    (other : Certificate left.holds right.holds (quote (project payload))) :
    (positiveCertificate (nativeReceipt left right oracle .confirm source firing value payload
      present found reading).observed).depth ≤ other.depth := positiveCertificate_least _ other

theorem refuted_excludes_every_future {Evidence : Type} (oracle : StepOracle Evidence)
    (source : Pattern) (firing : RuleFiring Evidence) (value : ContextualValue)
    (payload : Term sig [] Srt.pr)
    (present : firing ∈ applyRuleWithOracle oracle (environment (scopeGuard left right)) language 0
      (guardedComm .refute) source)
    (found : lookup firing.captured "q" = some value)
    (reading : instantiateValue? value 0 0 [] = some (encodeTerm payload))
    (future : Ctx sig) (env : Environment sig (TermQ rhoSourceE) [] future) :
    ¬ generated left.holds right.holds (model.substitution.substitute env (quote (project payload))) :=
  (nativeReceipt left right oracle .refute source firing value payload present found reading).sound future env

end

end Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts
