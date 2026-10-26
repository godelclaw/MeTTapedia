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
  exact scope_bind_returns state parameter value assignment

/-- The request a root match starts from, as the MeTTa body builds it. -/
theorem root_request_term (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (source : Pattern) :
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ⟨rule, spec, ambient, .left, [], 0, [], rule.left, source⟩ =
      .application "ScopedMatcherRequest" [InferenceCettaWire.AuthoredRule.rewriteTerm rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, .natural ambient, .symbol "RuleLeft", .symbol "LNil",
        .natural 0, .symbol "LNil", InferenceCettaWire.encodePattern rule.left, InferenceCettaWire.encodePattern source] :=
  rfl

namespace Interpreted

theorem evaluate_root_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.root depth bound type source index) outer)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (supported : ∀ rule spec, environment.language.rewrites[index]? = some rule → specification? environment index = some spec →
      admittedFor rule spec = true → checkOpenPatternWellSorted environment.language environment.free bound type source = true →
      requestReady ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.root depth bound type source index)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer (.root depth bound type source index) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have lookup := descent_row_returns InferenceCettaWire.AuthoredRule.rewriteTerm host index environment.language.rewrites
  cases depth with
  | zero =>
    descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluateRoot]
  | succ inner =>
    simp only [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluateRoot]
    split
    · rename_i declared
      have row := lookup
      simp only [declared] at row
      descent_interpreted_eval [view, count, row]
    · rename_i rule declared
      have row := lookup
      simp only [declared] at row
      have specification := descent_specification_returns host environment index
      split
      · rename_i specified
        have specRead := specification
        simp only [specified] at specRead
        descent_interpreted_eval [view, count, row, specRead] unfolding [InferenceCettaWire.AuthoredRule.rewriteTerm]
      · rename_i spec specified
        have specRead := specification
        simp only [specified] at specRead
        have admission := descent_binding_admitted_returns host rule spec
        split
        · rename_i admitted
          have sorting := Lowered.sorted host environment.language (environment.free.entriesOn footprint) bound type source
          simp only [Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot
            environment.language environment.free bound type source footprint covered] at sorting
          split
          · rename_i checked
            have boundSize := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host bound
            have started := operations.start host _ (supported rule spec declared specified admitted checked)
            rw [root_request_term] at started
            descent_interpreted_eval [view, count, row, specRead]
              unfolding [admitted, checked, RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
                InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
            all_goals descent_interpreted_body [admission, sorting, boundSize, started]
              unfolding [admitted, checked, RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
                InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
          · rename_i unchecked
            have failed : checkOpenPatternWellSorted environment.language environment.free bound type source = false :=
              Bool.eq_false_iff.mpr unchecked
            descent_interpreted_eval [view, count, row, specRead, admission, sorting]
              unfolding [admitted, failed, InferenceCettaWire.AuthoredRule.rewriteTerm]
        · rename_i rejected
          have failed : admittedFor rule spec = false := Bool.eq_false_iff.mpr rejected
          descent_interpreted_eval [view, count, row, specRead, admission] unfolding [failed, InferenceCettaWire.AuthoredRule.rewriteTerm]

#print axioms evaluate_root_returns


theorem evaluate_quantified_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (parameter : String) (body : Premise) (index : Nat)
    (elements : List Pattern) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.quantified depth context parameter body index elements initial) outer)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint (.quantified depth context parameter body index elements initial))
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.quantified depth context parameter body index elements initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.quantified depth context parameter body index elements initial) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  cases elements with
  | nil =>
    descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate,
      RetainedMatchingWire.quantifiedEventsTerm, InferenceCettaWire.encodePatterns]
  | cons element rest =>
    let assignment := bindParameter parameter (localValue context.bound element) initial
    have captured := Query.bound_parameter_free_within footprint parameter (localValue context.bound element) initial
      covered.2.1 (covered.2.2 element (by simp))
    have check := descent_check_assignment_returns host environment.language
      (environment.free.entriesOn footprint) context.bound context.rule context.spec assignment
    simp only [ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free context.bound
      context.rule context.spec assignment footprint (ConditionalEquationExecution.assignment_free_names_covered footprint _ captured)] at check
    have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
    have valued := descent_local_value_returns host context.bound element
    have boundParameter := descent_scope_bind_returns host parameter (localValue context.bound element) initial
    have quantified := descent_context_quantified_returns host context
    simp only [StructuralDescent.Scheduled.evaluate]
    split
    · rename_i valid
      change ConditionalEquationExecution.checkAssignment environment.language environment.free context.bound context.rule context.spec
        assignment = true at valid
      descent_interpreted_eval [view, count, bound, valued, boundParameter, quantified, check]
        unfolding [valid, assignment, Context.quantified, GeneralPremise.checkTypedAssignment,
          PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
          InferenceCettaWire.encodePatterns, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
    · rename_i invalid
      have failed : ConditionalEquationExecution.checkAssignment environment.language environment.free context.bound context.rule context.spec
          assignment = false := Bool.eq_false_iff.mpr invalid
      descent_interpreted_eval [view, count, bound, valued, boundParameter, quantified, check]
        unfolding [failed, assignment, Context.quantified, GeneralPremise.checkTypedAssignment,
          PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
          InferenceCettaWire.encodePatterns, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

#print axioms evaluate_quantified_returns


end Interpreted


theorem descent_evaluate_quantified_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise) (index : Nat)
    (elements : List Pattern) (initial : Assignment)
    (tail : Continuation environment (.quantified depth context parameter body index elements initial) outer)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint
      (.quantified depth context parameter body index elements initial)) :
    Evaluates state environment footprint (.quantified depth context parameter body index elements initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_quantified_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec footprint
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context parameter body index elements initial tail covered
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_root_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Continuation environment (.root depth bound type source index) outer)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    Evaluates state environment footprint (.root depth bound type source index) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_root_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec footprint
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth bound type source index tail
      (fun _ => True) (fun _ => True) (fun _ => True)
      (Interpreted.ordinary_matching_operations environment (environment.free.entriesOn footprint))
      (fun _ _ _ _ _ _ => True.intro) covered
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

#print axioms Interpreted.evaluate_root_returns
#print axioms Interpreted.evaluate_quantified_returns
#print axioms descent_evaluate_root_returns
#print axioms descent_evaluate_quantified_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
