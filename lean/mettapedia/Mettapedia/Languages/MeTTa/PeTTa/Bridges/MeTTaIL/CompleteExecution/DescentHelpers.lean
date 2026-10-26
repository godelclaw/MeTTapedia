import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentLower
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseQueryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseExecution
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFrames

/-!
# The premise helpers in the descent machine's runtime

The descent machine evaluates premises, matches roots and targets and asks queries through the
helper heads of the scoped source: specification lookup, binding admission, assignment checks,
matcher ticks, query expansion, instantiation, freshness, collections and local values. Each is
already proved in the scoped machine fragment or in a program below it; here each moves into the
descent machine's runtime as a call at values.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- Bind a call's values to names, then prove the call at the names. -/
syntax "metta_bound " " [" str,* "]" : tactic
macro_rules
  | `(tactic| metta_bound [$names,*]) => `(tactic|
      refine call_of_bound (by decide +kernel) (by decide) [$names,*] (by decide) rfl (by decide +kernel) ?_)

/-- The bound names read back the values. -/
syntax "metta_reads" : tactic
macro_rules
  | `(tactic| metta_reads) => `(tactic|
      simp [applySubst, Subst.lookup, List.zip, List.zipWith, List.find?, CettaWireAtom.applySubst_encode,
        CettaWire.encodeList_map, PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
        ScopedInstantiationExecution.instantiationValues])

theorem descent_row_returns {α : Type} (encoder : α → Term) (state : State) (index : Nat) (items : List α) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:row-at" [number index, encoded (encodeList encoder items)]) state
      (encoded (encodeOption encoder items[index]?)) := by
  metta_bound ["index", "values"]
  have lowered := lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical.row_returns
      (["index", "values"].zip [number index, encoded (encodeList encoder items)]) state index (items.map encoder)
      (.var "index") (.var "values") (by metta_reads))
  cases found : items[index]? <;> simpa [List.getElem?_map, found, encodeOption] using lowered

theorem descent_specification_returns (state : State) (environment : Environment) (index : Nat) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:specification" [number index,
        encoded (encodeList PremiseOperationsExecution.GeneralExecution.specificationTerm environment.specifications)])
      state (encoded (encodeOption InferenceCettaWire.AuthoredRule.bindingSpecTerm (specification? environment index))) := by
  metta_bound ["index", "specifications"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.specification_in_extension_returns
      RuleExecutionProgram.scopedMachineProgram PremiseOperationsExecution.GeneralExecution.AssembledLower.premise_agreement
      _ state environment index (.var "index") (.var "specifications") (by metta_reads))

theorem descent_binding_admitted_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:binding-admitted" [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)])
      state (Effects.boolean (admittedFor rule spec)) := by
  metta_bound ["rule", "spec"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.AdmissionLower.Assembly.admitted_captured_returns _ state rule spec
      (.var "rule") (.var "spec") (by metta_reads))

theorem descent_check_assignment_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:check-assignment"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment])
      state (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound rule spec assignment)) := by
  metta_bound ["declarations", "free", "bound", "rule", "spec", "assignment"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers.assignment_returns _ state language free bound
      rule spec assignment (.var "declarations") (.var "free") (.var "bound") (.var "rule") (.var "spec")
      (.var "assignment") (by metta_reads))

theorem descent_matcher_tick_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-matcher-tick"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request),
         encoded (RuleInstantiationExecution.GeneralExecution.matcherStateTerm machine)])
      state (encoded (RuleInstantiationExecution.GeneralExecution.matcherStateTerm
        (GeneralScopedMatchMachine.tick request machine))) := by
  metta_bound ["request", "matcher"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical.tick_returns _ state request machine
      (.var "request") (.var "matcher") (by metta_reads))

theorem descent_matcher_complete_returns (state : State) (machine : GeneralScopedMatchMachine.State) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-matcher-complete"
        [encoded (RuleInstantiationExecution.GeneralExecution.matcherStateTerm machine)])
      state (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  metta_bound ["matcher"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical.complete_returns _ state machine
      (.var "matcher") (by metta_reads))

theorem descent_query_expand_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (request : Query.Request)
    (task : Query.Task environment request) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:query-expand-in"
        [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint)),
         encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request),
         encoded (PremiseOperationsExecution.GeneralExecution.queryTaskTerm task)])
      state (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.QueryExecution.queryExpansionTerm
        (some (Query.expand environment request task)))) := by
  metta_bound ["environment", "request", "task"]
  exact PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.query_expand_captured_returns
    RuleExecutionProgram.interpretedPremiseProgram
    PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.interpreted_agreement
    PremiseOperationsExecution.GeneralExecution.QueryLower.interpreted_operations _ state environment request task
    (by simp [finiteProvider]) footprint provider captures (.var "environment") (.var "request") (.var "task")
    (by metta_reads)

theorem descent_query_obligations_returns (state : State) (reasons : List Query.Obligation) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:query-obligations"
        [encoded (encodeList PremiseOperationsExecution.GeneralExecution.queryObligationTerm reasons)])
      state (encoded (encodeList DescentCodec.obligationTerm
        (reasons.map StructuralDescent.Scheduled.Obligation.query))) := by
  metta_bound ["unresolved"]
  have lowered := lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.query_obligations_captured_returns
      RuleExecutionProgram.scopedMachineProgram
      PremiseOperationsExecution.GeneralExecution.AdmissionLower.Assembly.agreement
      (["unresolved"].zip [encoded (encodeList PremiseOperationsExecution.GeneralExecution.queryObligationTerm reasons)])
      state reasons (.var "unresolved") (by metta_reads))
  have same : encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm
      (reasons.map Execution.Obligation.query) =
      encodeList DescentCodec.obligationTerm (reasons.map StructuralDescent.Scheduled.Obligation.query) := by
    simp only [CettaWire.encodeList_map]
    rfl
  rw [← same]
  exact lowered

theorem descent_source_type_returns (state : State) (language : LanguageDef) (rule : RewriteRule) (source : Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:source-type"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
         encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule), encoded (InferenceCettaWire.encodePattern source)])
      state (encoded (encodeOption InferenceCettaWire.AuthoredRule.typeTerm (sourceType? language rule source))) := by
  metta_bound ["declarations", "rule", "source"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.source_type_returns _
      state language rule source (.var "declarations") (.var "rule") (.var "source") (by metta_reads))

theorem descent_instantiate_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-instantiate-at"
        [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
         encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path), number depth,
         assignmentValue assignment, encoded (InferenceCettaWire.encodePattern pattern)])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (instantiateAt? rule spec ambient site path depth assignment pattern))) := by
  metta_bound ["operation", "rule", "spec", "ambient", "site", "path", "depth", "assignment", "pattern"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.instantiate_returns _
      state rule spec ambient site path depth assignment pattern
      [.var "operation", .var "rule", .var "spec", .var "ambient", .var "site", .var "path", .var "depth",
        .var "assignment", .var "pattern"]
      (by metta_reads))

theorem descent_instantiate_value_returns (state : State) (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-instantiate-value"
        [encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value), number ambient, number depth,
         encoded (InferenceCettaWire.encodePatterns arguments)])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (instantiateValue? value ambient depth arguments))) := by
  metta_bound ["value", "ambient", "depth", "arguments"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.instantiate_value_returns
      _ state value ambient depth arguments (.var "value") (.var "ambient") (.var "depth") (.var "arguments")
      (by metta_reads))

theorem descent_binding_returns (state : State) (name : String) (assignment : Assignment) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:automata:binding" [encoded (.string name), assignmentValue assignment])
      state (encoded (RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm
        (ScopedRuleMatching.lookup assignment name))) := by
  metta_bound ["name", "assignment"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.binding_returns _
      state name assignment (.var "name") (.var "assignment") (by metta_reads))

theorem descent_fresh_returns (state : State) (name : String) (pattern : Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:fresh" [encoded (.string name), encoded (InferenceCettaWire.encodePattern pattern)])
      state (Effects.boolean (Substitution.isFresh name pattern)) := by
  metta_bound ["name", "pattern"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.fresh_returns _
      state name pattern (.var "name") (.var "pattern") (by metta_reads))

/-- Move a proved premise primitive through its checked source fragments. -/
syntax "metta_from_premise_source " term:max : tactic
macro_rules
  | `(tactic| metta_from_premise_source $fact) => `(tactic|
      exact lower_returns (by decide +kernel)
        (PremiseOperationsExecution.GeneralExecution.premise_returns_in_extension _
          PremiseOperationsExecution.GeneralExecution.AssembledLower.premise_agreement (by decide +kernel)
          (PremiseOperationsExecution.GeneralExecution.premise_previous_returns (by decide +kernel)
            (PremiseOperationsExecution.GeneralExecution.Base.previous_returns (by decide +kernel) $fact))))

theorem descent_collection_returns (state : State) (ambient : Nat) (assignment : Assignment) (name : String) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:scope-collection" [number ambient, assignmentValue assignment, encoded (.string name)])
      state (encoded (PremiseOperationsExecution.QuantifiedLocal.finiteCollectionOptionTerm
        (finiteCollection? ambient assignment name))) := by
  metta_bound ["ambient", "assignment", "collection"]
  metta_from_premise_source
    (PremiseOperationsExecution.QuantifiedLocal.finite_collection_captured_returns _ state ambient assignment name
      (.var "ambient") (.var "assignment") (.var "collection") (by metta_reads))

theorem descent_local_value_returns (state : State) (bound : List TypeExpr) (pattern : Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:scope-local-value" [number bound.length, encoded (InferenceCettaWire.encodePattern pattern)])
      state (encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm (localValue bound pattern))) := by
  metta_bound ["ambient", "element"]
  metta_from_premise_source
    (PremiseOperationsExecution.QuantifiedLocal.local_value_captured_returns _ state bound pattern
      (.var "ambient") (.var "element") (by metta_reads))

theorem descent_context_quantified_returns (state : State) (context : Context) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:context-quantified" [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context)])
      state (encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context.quantified)) := by
  metta_bound ["context"]
  exact lower_returns (by decide +kernel)
    (PremiseOperationsExecution.GeneralExecution.premise_returns_in_extension _
      PremiseOperationsExecution.GeneralExecution.AssembledLower.premise_agreement (by decide +kernel)
      (PremiseOperationsExecution.GeneralExecution.premise_previous_returns (by decide +kernel)
        (PremiseOperationsExecution.GeneralExecution.context_quantified_captured_returns _ state context
          (.var "context") (by metta_reads))))

namespace Interpreted

/-- Walk a captured evaluator body with the selected matching codecs. -/
syntax "descent_interpreted_body" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| descent_interpreted_body $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_eval [$facts,*] with descentProof_checked in descentProof_agreement
      unfolding [Library.bind, encodeList, encodeOption,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        InferenceCettaWire.AuthoredRule.premiseTerm, InferenceCettaWire.encodeList,
        PremiseOperationsExecution.GeneralExecution.environmentTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm,
        RetainedMatchingWire.Scheduled.continuationTerm, RetainedMatchingWire.Scheduled.resultTerm,
        RetainedMatchingWire.Scheduled.answerTerm, RetainedMatchingWire.Scheduled.expansionTerm,
        CompleteExecution.DescentCodec.goalTerm, CompleteExecution.DescentCodec.obligationTerm,
        RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.stepCallTerm,
        PremiseOperationsExecution.GeneralExecution.contextTerm, PremiseSchedulerExecution.schedulerExpansionTerm, $extra,*]))

/-- Enter the shared evaluator and walk its body with the selected codecs. -/
syntax "descent_interpreted_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| descent_interpreted_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in descentProof_checked using descentProof_agreement; descent_interpreted_body [$facts,*] unfolding [$extra,*]))

/-- The ordinary matcher specializes the shared native matching contract. -/
theorem ordinary_matching_operations (environment : Environment) (free : List (String × TypeExpr)) :
    RetainedMatchingWire.MatchingOperations descentLibrary.runtime MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)
      (fun _ => True) (fun _ => True) (fun _ => True) :=
  PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.ordinary_operations
    RuleExecutionProgram.interpretedPremiseProgram
    PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.interpreted_agreement
    PremiseOperationsExecution.GeneralExecution.QueryLower.interpreted_operations environment free

/-- Function equality also rewrites an encoder retained under list and option maps. -/
theorem ordinary_expansion_terms {environment : Environment} {outer : StructuralDescent.Scheduled.Goal} :
    (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.ordinaryCodec :
      Scheduler.Expansion (StructuralDescent.Scheduled.Task environment outer)
        (StructuralDescent.Scheduled.Result environment outer) StructuralDescent.Scheduled.Obligation → Term) =
      CompleteExecution.DescentCodec.expansionTerm :=
  funext RetainedMatchingWire.Scheduled.ordinary_expansion

theorem ordinary_task_terms {environment : Environment} {outer : StructuralDescent.Scheduled.Goal} :
    (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.ordinaryCodec :
      StructuralDescent.Scheduled.Task environment outer → Term) = CompleteExecution.DescentCodec.taskTerm :=
  funext RetainedMatchingWire.Scheduled.ordinary_task

end Interpreted

#print axioms descent_query_expand_returns
#print axioms Interpreted.ordinary_matching_operations
#print axioms Interpreted.ordinary_expansion_terms
#print axioms Interpreted.ordinary_task_terms

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
