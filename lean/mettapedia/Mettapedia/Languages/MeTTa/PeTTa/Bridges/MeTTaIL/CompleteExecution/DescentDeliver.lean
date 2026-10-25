import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentLower
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentMachine
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledEquations
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFootprint

/-!
# Delivering results in the descent machine

`gslt:descent:deliver` passes a result to its continuation: the next premise, the list of
premises, a quantifier, a quantified element, a root body, a searched root, or a step call.
The root body and step call cases are delegated to their own heads.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open StructuralDescent.Scheduled (Goal Result Task Obligation Continuation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

/-- A head that delivers a result to a continuation returns the delivered expansion. -/
def Delivers (head : String) (state : State) (environment : Environment) (free : List (String × TypeExpr))
    {goal outer : Goal} (result : Result environment goal) (tail : Continuation environment goal outer) : Prop :=
  PureReturns descentLibrary.runtime [] state
    (apply head [environmentValue environment free, encoded (resultTerm result), encoded (continuationTerm tail)])
    state (encoded (encodeOption expansionTerm (some (StructuralDescent.Scheduled.delivered environment outer result tail))))

/-- Whether a continuation is a root body or a step call, the two delegated kinds. -/
def delegated {environment : Environment} {goal outer : Goal} : Continuation environment goal outer → Bool
  | .rootBody .. => true
  | .stepped .. => true
  | _ => false

theorem descent_deliver_inline_returns (state : State) (environment : Environment) (free : List (String × TypeExpr))
    {goal outer : Goal} (result : Result environment goal) (tail : Continuation environment goal outer)
    (inline : delegated tail = false) :
    Delivers "gslt:descent:deliver" state environment free result tail := by
  unfold Delivers
  cases tail with
  | done goal =>
    metta_call descent_checked
    metta_eval unfolding [continuationTerm, resultTerm, goalTerm, expansionTerm, schedulerExpansionTerm, encodeList,
      encodeOption]
  | nextPremise depth context premise premises initial tail =>
    cases result with
    | premise assignment event valid =>
      metta_call descent_checked
      metta_eval [descent_context_next_returns state context] with descent_checked
        unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm,
          encodeList, encodeOption]
  | prepend depth context premise premises initial middle event head tail =>
    cases result with
    | premises assignment events valid =>
      metta_call descent_checked
      metta_eval unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm,
        taskTerm, encodeList, encodeOption, PremiseOperationsExecution.GeneralExecution.eventsTerm]
  | quantifier depth context collection parameter body initial kind elements read tail =>
    cases result with
    | quantified assignment events valid =>
      rw [StructuralDescent.Scheduled.delivered_quantifier]
      metta_call descent_checked
      metta_eval unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm,
        taskTerm, encodeList, encodeOption,
        PremiseOperationsExecution.GeneralExecution.contextTerm, PremiseOperationsExecution.GeneralExecution.eventTerm,
        InferenceCettaWire.AuthoredRule.premiseTerm]
  | element depth context parameter body index element elements initial localTyped tail =>
    cases result with
    | premise assignment event valid =>
      metta_call descent_checked
      metta_eval with descent_checked
        unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm,
          encodeList, encodeOption]
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
    cases result with
    | quantified assignment events valid =>
      rw [StructuralDescent.Scheduled.delivered_prependElement]
      metta_call descent_checked
      metta_eval unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm,
        taskTerm, encodeList, encodeOption,
        PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm, PremiseOperationsExecution.GeneralExecution.eventsTerm,
        InferenceCettaWire.encodePatterns]
  | searchedRoot depth bound type source index limit earlier tail =>
    cases result with
    | root trace captured completed events target valid =>
      metta_call descent_checked
      metta_eval unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm,
        taskTerm, encodeList, encodeOption]
  | rootBody => simp [delegated] at inline
  | stepped => simp [delegated] at inline

/-- `gslt:descent:stepped-deliver` starts the target match of a step call. -/
@[metta_head "gslt:descent:stepped-deliver"]
theorem descent_stepped_deliver_returns (state : State) (environment : Environment) (free : List (String × TypeExpr))
    {outer : Goal} (depth : Nat) (call : StructuralDescent.Scheduled.StepCall environment)
    (tail : Continuation environment (.premise depth call.context call.premise call.initial) outer)
    (result : Result environment (.steps depth (call.binders ++ call.context.bound) call.type call.source
      environment.language.rewrites.length)) :
    Delivers "gslt:descent:stepped-deliver" state environment free result (.stepped depth call tail) := by
  unfold Delivers
  cases result with
  | steps index trace captured completed events target earlier valid =>
    rw [StructuralDescent.Scheduled.delivered_stepped]
    obtain ⟨context, premise, initial, binders, type, source, targetSchema, conclude⟩ := call
    obtain ⟨ruleIndex, rule, spec, bound, premiseIndex, quantifierDepth⟩ := context
    metta_call descent_checked
    metta_eval [descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state binders,
        descent_matcher_start_returns state ⟨rule, spec, bound.length, .premise premiseIndex quantifierDepth 1, [],
          binders.length, initial, targetSchema, target⟩]
      with descent_checked
      unfolding [continuationTerm, resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm,
        encodeList, encodeOption, PremiseOperationsExecution.GeneralExecution.stepCallTerm,
        PremiseOperationsExecution.GeneralExecution.contextTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, InferenceCettaWire.AuthoredRule.siteTerm,
        GeneralPremise.Context.site]

/-- `gslt:descent:root-body-deliver` finishes a rule firing: the scoped reduct, then its sort check. -/
@[metta_head "gslt:descent:root-body-deliver"]
theorem descent_root_body_deliver_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
    {rule : RewriteRule} {spec : RuleBindingSpec} (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted environment.language environment.free
      bound type source)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left source trace captured)
    (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)
    (result : Result environment (.premises depth ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured))
    (produced : StructuralDescent.Scheduled.resultFreeWithin footprint result) :
    Delivers "gslt:descent:root-body-deliver" state environment (environment.free.entriesOn footprint) result
      (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
        capturedTyped tail) := by
  unfold Delivers
  cases result with
  | premises completed events valid =>
    cases converted : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule) rule spec
        bound.length completed with
    | none =>
      rw [StructuralDescent.Scheduled.delivered_rootBody_none declared specified admitted sorted matched capturedTyped
        valid tail converted]
      metta_call descent_checked
      metta_eval [Lowered.selection state environment.reflection rule,
          descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound,
          Lowered.reduct state environment.reflection rule spec bound.length completed]
        with descent_checked
        unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm, continuationTerm,
          resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm, obligationTerm, encodeList,
          encodeOption, converted]
    | some target =>
      cases checked : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted environment.language
          environment.free bound type target with
      | true =>
        rw [StructuralDescent.Scheduled.delivered_rootBody_sorted declared specified admitted sorted matched
          capturedTyped valid tail converted checked]
        have checkedTable := checked
        rw [← Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot environment.language environment.free
          bound type target footprint (ScopedReflectiveExecution.selected_reduct_free_within footprint
            environment.reflection rule spec admitted bound.length completed target produced.2 converted)] at checkedTable
        metta_call descent_checked
        metta_eval [Lowered.selection state environment.reflection rule,
            descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound,
            Lowered.reduct state environment.reflection rule spec bound.length completed,
            Lowered.sorted state environment.language (environment.free.entriesOn footprint) bound type target]
          with descent_checked
          unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm, continuationTerm,
            resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm, encodeList,
            encodeOption, converted, checkedTable]
      | false =>
        rw [StructuralDescent.Scheduled.delivered_rootBody_unsorted declared specified admitted sorted matched
          capturedTyped valid tail converted checked]
        have checkedTable := checked
        rw [← Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot environment.language environment.free
          bound type target footprint (ScopedReflectiveExecution.selected_reduct_free_within footprint
            environment.reflection rule spec admitted bound.length completed target produced.2 converted)] at checkedTable
        metta_call descent_checked
        metta_eval [Lowered.selection state environment.reflection rule,
            descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state bound,
            Lowered.reduct state environment.reflection rule spec bound.length completed,
            Lowered.sorted state environment.language (environment.free.entriesOn footprint) bound type target]
          with descent_checked
          unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm, continuationTerm,
            resultTerm, answerTerm, goalTerm, expansionTerm, schedulerExpansionTerm, taskTerm, encodeList,
            encodeOption, converted, checkedTable]

/-- **`gslt:descent:deliver` is `delivered`**, for every continuation. -/
@[metta_head "gslt:descent:deliver"]
theorem descent_deliver_returns (state : State) (environment : Environment) (footprint : List String)
    {goal outer : Goal} (result : Result environment goal) (tail : Continuation environment goal outer)
    (produced : StructuralDescent.Scheduled.resultFreeWithin footprint result) :
    Delivers "gslt:descent:deliver" state environment (environment.free.entriesOn footprint) result tail := by
  cases inline : delegated tail with
  | false => exact descent_deliver_inline_returns state environment _ result tail inline
  | true =>
    unfold Delivers
    cases tail with
    | rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
        capturedTyped tail =>
      metta_call descent_checked
      metta_eval [descent_root_body_deliver_returns state environment footprint declared specified admitted sorted
          matched capturedTyped tail result produced]
        with descent_checked unfolding [continuationTerm]
    | stepped depth call tail =>
      metta_call descent_checked
      metta_eval [descent_stepped_deliver_returns state environment (environment.free.entriesOn footprint) depth call tail result]
        with descent_checked unfolding [continuationTerm]
    | _ => simp [delegated] at inline

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
