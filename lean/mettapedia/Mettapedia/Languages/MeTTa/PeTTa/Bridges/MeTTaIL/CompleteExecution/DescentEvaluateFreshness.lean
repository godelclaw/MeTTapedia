import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentEvaluate

/-!
# Evaluating freshness tests

A freshness test reads its name from the assignment (the name itself when unbound, the atom its
value instantiates to otherwise), instantiates its subject, and delivers when the name does not
occur free in the subject.
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

theorem descent_evaluate_freshness_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (condition : FreshnessCondition) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.freshness condition) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.freshness condition) initial) tail := by
  unfold Evaluates
  obtain ⟨name, term⟩ := condition
  have rewrites := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites
  have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound
  have binding := descent_binding_returns state name initial
  have subject := descent_instantiate_returns state context.rule context.spec context.bound.length
    (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term
  cases looked : ScopedRuleMatching.lookup initial name with
  | none =>
    cases interpreted : instantiateAt? context.rule context.spec context.bound.length
        (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term with
    | none =>
      rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
        (by simp [freshnessSubject?, freshnessName?, looked, interpreted])]
      descent_eval_bound [rewrites, bound, binding, subject]
        unfolding [looked, interpreted, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
          MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm]
    | some actual =>
      rw [StructuralDescent.Scheduled.evaluate_freshness_some _ name actual tail
        (by simp [freshnessSubject?, freshnessName?, looked, interpreted])]
      have tested := descent_fresh_returns state name actual
      by_cases fresh : Substitution.isFresh name actual = true
      · rw [dif_pos fresh]
        descent_eval_bound [rewrites, bound, binding, subject, tested]
          unfolding [looked, interpreted, fresh, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
            MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm,
            PremiseOperationsExecution.GeneralExecution.eventTerm]
      · rw [dif_neg fresh]
        have stale : Substitution.isFresh name actual = false := by simpa using fresh
        descent_eval_bound [rewrites, bound, binding, subject, tested]
          unfolding [looked, interpreted, stale, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
            MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.AuthoredRule.siteTerm,
            PremiseOperationsExecution.GeneralExecution.eventTerm]
  | some stored =>
    have valuedFact := descent_instantiate_value_returns state stored context.bound.length 0 []
    cases valued : instantiateValue? stored context.bound.length 0 [] with
    | none =>
      rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
        (by simp [freshnessSubject?, freshnessName?, looked, valued])]
      descent_eval_bound [rewrites, bound, binding, valuedFact]
        unfolding [looked, valued, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
          MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns]
    | some value =>
      cases value with
      | fvar atom =>
        have tested := fun actual => descent_fresh_returns state atom actual
        cases interpreted : instantiateAt? context.rule context.spec context.bound.length
            (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial term with
        | none =>
          rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
            (by simp [freshnessSubject?, freshnessName?, looked, valued, interpreted])]
          descent_eval_bound [rewrites, bound, binding, valuedFact, subject]
            unfolding [looked, valued, interpreted, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
              MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
              InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm]
        | some actual =>
          rw [StructuralDescent.Scheduled.evaluate_freshness_some _ atom actual tail
            (by simp [freshnessSubject?, freshnessName?, looked, valued, interpreted])]
          have tested := descent_fresh_returns state atom actual
          by_cases fresh : Substitution.isFresh atom actual = true
          · rw [dif_pos fresh]
            descent_eval_bound [rewrites, bound, binding, valuedFact, subject, tested]
              unfolding [looked, valued, interpreted, fresh,
                RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
                MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
                InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm,
                PremiseOperationsExecution.GeneralExecution.eventTerm]
          · rw [dif_neg fresh]
            have stale : Substitution.isFresh atom actual = false := by simpa using fresh
            descent_eval_bound [rewrites, bound, binding, valuedFact, subject, tested]
              unfolding [looked, valued, interpreted, stale,
                RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
                MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
                InferenceCettaWire.encodePattern, InferenceCettaWire.AuthoredRule.siteTerm,
                PremiseOperationsExecution.GeneralExecution.eventTerm]
      | _ =>
        rw [StructuralDescent.Scheduled.evaluate_freshness_none _ tail
          (by simp [freshnessSubject?, freshnessName?, looked, valued])]
        descent_eval_bound [rewrites, bound, binding, valuedFact]
          unfolding [looked, valued, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map,
            MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePatterns,
            InferenceCettaWire.encodePattern]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
