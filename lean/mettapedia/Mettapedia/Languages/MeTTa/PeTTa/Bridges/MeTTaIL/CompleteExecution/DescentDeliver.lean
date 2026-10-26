import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentHelpers
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
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
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
def delegated {matcher : MatchingExecution} {environment : Environment} {goal outer : Goal} :
    StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer → Bool
  | .rootBody .. => true
  | .stepped .. => true
  | _ => false

namespace Interpreted

def deliveryMatchRequests {matcher : MatchingExecution} {environment : Environment}
    {goal outer : StructuralDescent.Scheduled.Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer) :
    List GeneralScopedMatchMachine.Request :=
  match tail with
  | .stepped _ call _ =>
    match result with
    | .steps _ _ _ _ _ target _ _ =>
      [⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
        [], call.binders.length, call.initial, call.targetSchema, target⟩]
  | _ => []

def deliveryAssignments {matcher : MatchingExecution} {environment : Environment}
    {goal outer : StructuralDescent.Scheduled.Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer) : List Assignment :=
  match tail with
  | .rootBody .. =>
    match result with
    | .premises completed _ _ => [completed]
  | _ => []

theorem delivered_inline_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) {goal outer : Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer)
    (inline : delegated tail = false) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:deliver"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.resultTerm codec result),
        encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.delivered environment outer result tail)))) := by
  cases tail with
  | done goal =>
    descent_interpreted_eval unfolding [StructuralDescent.Scheduled.delivered]
  | nextPremise depth context premise premises initial tail =>
    cases result with
    | premise assignment event valid =>
      have next := descent_context_next_returns host context
      descent_interpreted_eval [next] unfolding [StructuralDescent.Scheduled.delivered]
  | prepend depth context premise premises initial middle event head tail =>
    cases result with
    | premises assignment events valid =>
      rw [StructuralDescent.Scheduled.delivered_prepend]
      descent_interpreted_eval unfolding [RetainedMatchingWire.eventsTerm]
  | quantifier depth context collection parameter body initial kind elements read tail =>
    cases result with
    | quantified assignment events valid =>
      descent_interpreted_eval unfolding [StructuralDescent.Scheduled.delivered, RetainedMatchingWire.eventTerm]
  | element depth context parameter body index element elements initial localTyped tail =>
    cases result with
    | premise assignment event valid =>
      descent_interpreted_eval unfolding [StructuralDescent.Scheduled.delivered]
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
    cases result with
    | quantified assignment events valid =>
      descent_interpreted_eval unfolding [StructuralDescent.Scheduled.delivered, RetainedMatchingWire.quantifiedEventsTerm,
        RetainedMatchingWire.eventsTerm, InferenceCettaWire.encodePatterns]
  | searchedRoot depth bound type source index limit earlier tail =>
    cases result with
    | root trace captured completed events target valid =>
      descent_interpreted_eval unfolding [StructuralDescent.Scheduled.delivered]
  | rootBody => simp [delegated] at inline
  | stepped => simp [delegated] at inline

theorem root_body_deliver_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule) (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted environment.language environment.free bound type source)
    (trace : List matcher.Choice) (captured completed : Assignment) (events : List (Event matcher.Choice))
    (matched : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ trace captured)
    (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
    (valid : GeneralPremise.Interpreted.PremisesHold matcher.meaning environment ⟨index, rule, spec, bound, 0, 0⟩
      rule.premises captured completed events)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (produced : assignmentFreeWithin footprint completed)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:root-body-deliver" [encoded profile,
      encoded (RetainedMatchingWire.Scheduled.resultTerm codec (.premises (depth := depth) completed events valid)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec
        (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched capturedTyped tail))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.delivered environment outer (.premises (depth := depth) completed events valid)
          (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched capturedTyped tail))))) := by
  have selected := Lowered.selection host environment.reflection rule
  have bounded := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host bound
  have reduced := Lowered.reduct host environment.reflection rule spec bound.length completed
  simp only [StructuralDescent.Scheduled.delivered]
  split
  · rename_i converted
    have read := reduced
    simp only [converted] at read
    descent_interpreted_eval [view, selected, bounded, read]
      unfolding [CompleteExecution.DescentCodec.typesTerm]
  · rename_i target converted
    have read := reduced
    simp only [converted] at read
    have targetWithin := ScopedReflectiveExecution.selected_reduct_free_within footprint environment.reflection rule spec admitted
      bound.length completed target produced converted
    have checked := Lowered.sorted host environment.language (environment.free.entriesOn footprint) bound type target
    simp only [Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot
      environment.language environment.free bound type target footprint targetWithin] at checked
    split
    · rename_i validTarget
      descent_interpreted_eval [view, selected, bounded, read, checked]
        unfolding [validTarget, CompleteExecution.DescentCodec.typesTerm]
    · rename_i invalidTarget
      have failed : checkOpenPatternWellSorted environment.language environment.free bound type target = false :=
        Bool.eq_false_iff.mpr invalidTarget
      descent_interpreted_eval [view, selected, bounded, read, checked]
        unfolding [failed, CompleteExecution.DescentCodec.typesTerm]

#print axioms root_body_deliver_returns


theorem stepped_deliver_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) {outer : StructuralDescent.Scheduled.Goal} (depth : Nat)
    (call : GeneralPremise.Execution.StepCall environment matcher)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth call.context call.premise call.initial) outer)
    (index : Nat) (trace : List matcher.Choice) (captured completed : Assignment)
    (events : List (Event matcher.Choice)) (target : Pattern) (earlier : index < environment.language.rewrites.length)
    (valid : GeneralPremise.Interpreted.RootFiring matcher.meaning environment (call.binders ++ call.context.bound)
      call.type call.source index trace captured completed events target)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (ready : requestReady ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
      [], call.binders.length, call.initial, call.targetSchema, target⟩) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:stepped-deliver" [encoded profile,
      encoded (RetainedMatchingWire.Scheduled.resultTerm codec (.steps (depth := depth) index trace captured completed events target earlier valid)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec (.stepped depth call tail))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.delivered environment outer
          (.steps (depth := depth) index trace captured completed events target earlier valid) (.stepped depth call tail))))) := by
  have ambient := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host call.context.bound
  have localSize := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host call.binders
  have started := operations.start host _ ready
  descent_interpreted_eval [ambient, localSize, started]
    unfolding [StructuralDescent.Scheduled.delivered, PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, InferenceCettaWire.AuthoredRule.siteTerm, Context.site]

#print axioms stepped_deliver_returns

theorem delivery_assignments_free (environment : Environment) (footprint : List String)
    {matcher : MatchingExecution} {goal outer : Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer)
    (free : StructuralDescent.Scheduled.resultFreeWithin footprint result) :
    ∀ assignment ∈ deliveryAssignments result tail, assignmentFreeWithin footprint assignment := by
  cases tail <;> try simp [deliveryAssignments]
  case rootBody =>
    cases result with
    | premises completed events valid =>
      intro assignment member
      rcases List.mem_singleton.mp member with rfl
      exact free.2

theorem delivered_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {goal outer : StructuralDescent.Scheduled.Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (supported : ∀ request ∈ deliveryMatchRequests result tail, requestReady request)
    (produced : ∀ assignment ∈ deliveryAssignments result tail, assignmentFreeWithin footprint assignment)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:deliver" [encoded profile,
      encoded (RetainedMatchingWire.Scheduled.resultTerm codec result),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.delivered environment outer result tail)))) := by
  cases inline : delegated tail with
  | false => exact delivered_inline_returns host environment matcher codec profile result tail inline
  | true =>
    cases tail with
      | rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched capturedTyped tail =>
        cases result with
        | premises completed events valid =>
          have completedWithin := produced completed (by simp [deliveryAssignments])
          have finished := root_body_deliver_returns host environment matcher codec footprint profile depth bound type source index
            rule spec declared specified admitted sorted trace captured completed events matched capturedTyped valid tail completedWithin view
          descent_interpreted_eval [finished] unfolding [RetainedMatchingWire.Scheduled.continuationTerm]
      | stepped depth call tail =>
        cases result with
        | steps index trace captured completed events target earlier valid =>
          have ready := supported
            ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
              [], call.binders.length, call.initial, call.targetSchema, target⟩ (by simp [deliveryMatchRequests])
          have stepped := stepped_deliver_returns host environment matcher codec profile depth call tail index trace captured completed events
            target earlier valid requestReady stateReady valueReady operations ready
          descent_interpreted_eval [stepped] unfolding [RetainedMatchingWire.Scheduled.continuationTerm]
      | _ => simp [delegated] at inline

end Interpreted

theorem descent_deliver_inline_returns (state : State) (environment : Environment) (free : List (String × TypeExpr))
    {goal outer : Goal} (result : Result environment goal) (tail : Continuation environment goal outer)
    (inline : delegated tail = false) :
    Delivers "gslt:descent:deliver" state environment free result tail := by
  unfold Delivers
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_result,
    RetainedMatchingWire.Scheduled.ordinary_continuation, Interpreted.ordinary_expansion_terms] using
    Interpreted.delivered_inline_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)
      result tail inline

theorem descent_stepped_deliver_returns (state : State) (environment : Environment) (free : List (String × TypeExpr))
    {outer : Goal} (depth : Nat) (call : StructuralDescent.Scheduled.StepCall environment)
    (tail : Continuation environment (.premise depth call.context call.premise call.initial) outer)
    (result : Result environment (.steps depth (call.binders ++ call.context.bound) call.type call.source
      environment.language.rewrites.length)) :
    Delivers "gslt:descent:stepped-deliver" state environment free result (.stepped depth call tail) := by
  unfold Delivers
  cases result with
  | steps index trace captured completed events target earlier valid =>
    simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_result,
      RetainedMatchingWire.Scheduled.ordinary_continuation, Interpreted.ordinary_expansion_terms] using
      Interpreted.stepped_deliver_returns state environment MatchingExecution.ordinary
        RetainedMatchingWire.ordinaryCodec (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)
        depth call tail index trace captured completed events target earlier valid
        (fun _ => True) (fun _ => True) (fun _ => True)
        (Interpreted.ordinary_matching_operations environment free) True.intro

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
    simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_result,
      RetainedMatchingWire.Scheduled.ordinary_continuation, Interpreted.ordinary_expansion_terms] using
      Interpreted.root_body_deliver_returns state environment MatchingExecution.ordinary
        RetainedMatchingWire.ordinaryCodec footprint
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))
        depth bound type source index rule spec declared specified admitted sorted trace captured completed events
        matched capturedTyped valid tail produced.2
        (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_deliver_returns (state : State) (environment : Environment) (footprint : List String)
    {goal outer : Goal} (result : Result environment goal) (tail : Continuation environment goal outer)
    (produced : StructuralDescent.Scheduled.resultFreeWithin footprint result) :
    Delivers "gslt:descent:deliver" state environment (environment.free.entriesOn footprint) result tail := by
  unfold Delivers
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_result,
    RetainedMatchingWire.Scheduled.ordinary_continuation, Interpreted.ordinary_expansion_terms] using
    Interpreted.delivered_returns state environment MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
      footprint (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))
      result tail (fun _ => True) (fun _ => True) (fun _ => True)
      (Interpreted.ordinary_matching_operations environment (environment.free.entriesOn footprint))
      (fun _ _ => True.intro) (Interpreted.delivery_assignments_free environment footprint result tail produced)
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

#print axioms Interpreted.delivered_inline_returns
#print axioms Interpreted.root_body_deliver_returns
#print axioms Interpreted.stepped_deliver_returns
#print axioms Interpreted.delivered_returns
#print axioms Interpreted.delivery_assignments_free
#print axioms descent_deliver_inline_returns
#print axioms descent_stepped_deliver_returns
#print axioms descent_root_body_deliver_returns
#print axioms descent_deliver_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
