import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentEvaluate

/-!
# Evaluating quantified elements and roots

A quantified element binds the parameter to the element's local value and checks the extended
assignment. A root looks up its rule and binding specification, checks admission and the
source's sort, and starts the matcher one level of depth down. Both checks read the footprint
snapshot of the free-type table, which agrees with the environment on every name the goal
mentions.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open StructuralDescent.Scheduled (Goal Result Task Obligation Continuation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

theorem descent_scope_bind_returns (state : State) (parameter : String) (value : ContextualValue)
    (assignment : Assignment) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:scope-bind" [encoded (.string parameter), contextualValue value, assignmentValue assignment])
      state (assignmentValue (bindParameter parameter value assignment)) := by
  metta_lift descent_checked ["parameter", "value", "assignment"]
    (by metta_lift typed_checked ["parameter", "value", "assignment"]
      (scope_bind_returns state parameter value assignment))

theorem descent_evaluate_quantified_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise) (index : Nat)
    (elements : List Pattern) (initial : Assignment)
    (tail : Continuation environment (.quantified depth context parameter body index elements initial) outer)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint
      (.quantified depth context parameter body index elements initial)) :
    Evaluates state environment footprint (.quantified depth context parameter body index elements initial) tail := by
  unfold Evaluates
  have rewrites := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites
  cases elements with
  | nil =>
    descent_eval [rewrites]
      unfolding [StructuralDescent.Scheduled.evaluate, PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm,
        InferenceCettaWire.encodePatterns]
  | cons element rest =>
    have boundCovered := Query.bound_parameter_free_within footprint parameter (localValue context.bound element)
      initial covered.2.1 (covered.2.2 element (by simp))
    have snapshot := ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
      context.bound context.rule context.spec (bindParameter parameter (localValue context.bound element) initial)
      footprint (ConditionalEquationExecution.assignment_free_names_covered footprint _ boundCovered)
    have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound
    have localFact := descent_local_value_returns state context.bound element
    have bind := descent_scope_bind_returns state parameter (localValue context.bound element) initial
    have quantified := descent_context_quantified_returns state context
    have check := descent_check_assignment_returns state environment.language (environment.free.entriesOn footprint)
      context.bound context.rule context.spec (bindParameter parameter (localValue context.bound element) initial)
    cases checked : checkTypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial) with
    | false =>
      rw [StructuralDescent.Scheduled.evaluate_quantified_unchecked tail checked]
      have answered : ConditionalEquationExecution.checkAssignment environment.language
          (FreeTypeContext.ofList (environment.free.entriesOn footprint)) context.bound context.rule context.spec
          (bindParameter parameter (localValue context.bound element) initial) = false := by
        rw [snapshot]
        exact checked
      descent_eval_bound [rewrites, bound, localFact, bind, quantified, check]
        unfolding [answered, contextualValue, InferenceCettaWire.encodePatterns]
    | true =>
      rw [StructuralDescent.Scheduled.evaluate_quantified_checked tail checked]
      have answered : ConditionalEquationExecution.checkAssignment environment.language
          (FreeTypeContext.ofList (environment.free.entriesOn footprint)) context.bound context.rule context.spec
          (bindParameter parameter (localValue context.bound element) initial) = true := by
        rw [snapshot]
        exact checked
      descent_eval_bound [rewrites, bound, localFact, bind, quantified, check]
        unfolding [answered, contextualValue, Context.quantified, InferenceCettaWire.encodePatterns]

/-- The request a root match starts from, as the MeTTa body builds it. -/
theorem root_request_term (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (source : Pattern) :
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ⟨rule, spec, ambient, .left, [], 0, [], rule.left, source⟩ =
      .application "ScopedMatcherRequest" [InferenceCettaWire.AuthoredRule.rewriteTerm rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, .natural ambient, .symbol "RuleLeft", .symbol "LNil",
        .natural 0, .symbol "LNil", InferenceCettaWire.encodePattern rule.left, InferenceCettaWire.encodePattern source] :=
  rfl

theorem descent_evaluate_root_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Continuation environment (.root depth bound type source index) outer)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    Evaluates state environment footprint (.root depth bound type source index) tail := by
  unfold Evaluates
  have rewrites := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites
  have row := descent_row_returns InferenceCettaWire.AuthoredRule.rewriteTerm state index environment.language.rewrites
  cases depth with
  | zero =>
    rw [StructuralDescent.Scheduled.evaluate_root_zero]
    descent_eval [rewrites]
  | succ inner =>
    cases declared : environment.language.rewrites[index]? with
    | none =>
      rw [StructuralDescent.Scheduled.evaluate_root_unavailable tail declared]
      descent_eval [rewrites, row] unfolding [declared]
    | some rule =>
      have specification := descent_specification_returns state environment index
      cases specified : specification? environment index with
      | none =>
        rw [StructuralDescent.Scheduled.evaluate_root_unspecified tail declared specified]
        descent_eval [rewrites, row, specification]
          unfolding [declared, specified, InferenceCettaWire.AuthoredRule.rewriteTerm]
      | some spec =>
        rw [StructuralDescent.Scheduled.evaluate_root_specified tail declared specified]
        have admission := descent_binding_admitted_returns state rule spec
        by_cases admitted : admittedFor rule spec = true
        · rw [dif_pos admitted]
          have snapshot := Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot environment.language
            environment.free bound type source footprint covered
          have sorting := Lowered.sorted state environment.language (environment.free.entriesOn footprint) bound type source
          have bounds := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound
          have start := descent_matcher_start_returns state
            ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
          by_cases checked : checkOpenPatternWellSorted environment.language environment.free bound type source = true
          · rw [dif_pos checked]
            descent_eval_bound [rewrites, row, specification, admission, sorting, bounds, start]
              unfolding [declared, specified, admitted, snapshot, checked, InferenceCettaWire.AuthoredRule.rewriteTerm,
                root_request_term, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
          · rw [dif_neg checked]
            have unchecked : checkOpenPatternWellSorted environment.language environment.free bound type source = false := by
              simpa using checked
            descent_eval_bound [rewrites, row, specification, admission, sorting]
              unfolding [declared, specified, admitted, snapshot, unchecked, InferenceCettaWire.AuthoredRule.rewriteTerm]
        · rw [dif_neg admitted]
          have rejected : admittedFor rule spec = false := by simpa using admitted
          descent_eval_bound [rewrites, row, specification, admission]
            unfolding [declared, specified, rejected, InferenceCettaWire.AuthoredRule.rewriteTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
