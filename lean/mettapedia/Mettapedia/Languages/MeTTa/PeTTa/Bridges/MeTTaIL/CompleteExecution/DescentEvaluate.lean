import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentHelpers
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentMachine
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledEvaluateEquations
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFootprint

/-!
# Evaluating goals in the descent machine

`gslt:descent:evaluate` opens a goal: a premise (a query, a freshness test, a quantifier, a
congruence step or a scoped step), a list of premises, a quantified element, a root, or a search
of the children of a source. The environment's free-type table is its snapshot on a footprint
that covers the goal, so each lookup it makes is the environment's own.
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

/-- What `gslt:descent:evaluate` returns: the expansion of a goal. -/
def Evaluates (state : State) (environment : Environment) (footprint : List String) {outer : Goal}
    (goal : Goal) (tail : Continuation environment goal outer) : Prop :=
  PureReturns descentLibrary.runtime [] state
    (apply "gslt:descent:evaluate" [environmentValue environment (environment.free.entriesOn footprint),
      encoded (goalTerm goal), encoded (continuationTerm tail)])
    state (encoded (encodeOption expansionTerm (some (StructuralDescent.Scheduled.evaluate environment outer goal tail))))

/-- Unfold an evaluate call and walk its body with the descent machine's codecs. -/
syntax "descent_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| descent_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call descent_checked; metta_eval [$facts,*] with descent_checked
        unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
          PremiseOperationsExecution.GeneralExecution.providerTerm, continuationTerm, resultTerm, answerTerm, goalTerm,
          expansionTerm, schedulerExpansionTerm, taskTerm, obligationTerm, encodeList, encodeOption,
          PremiseOperationsExecution.GeneralExecution.contextTerm, PremiseOperationsExecution.GeneralExecution.stepCallTerm,
          InferenceCettaWire.AuthoredRule.premiseTerm, InferenceCettaWire.encodeList, $extra,*]))

/-- `descent_eval`, also reading case bodies that `let*` bound under a substitution. -/
syntax "descent_eval_bound" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| descent_eval_bound $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| descent_eval [$facts,*] unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, $extra,*])

theorem descent_evaluate_premises_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (premises : List Premise) (initial : Assignment)
    (tail : Continuation environment (.premises depth context premises initial) outer) :
    Evaluates state environment footprint (.premises depth context premises initial) tail := by
  unfold Evaluates
  cases premises with
  | nil =>
    metta_call descent_checked
    metta_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites]
      with descent_checked
      unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm, continuationTerm, resultTerm, answerTerm, goalTerm,
        expansionTerm, schedulerExpansionTerm, taskTerm, encodeList, encodeOption, StructuralDescent.Scheduled.evaluate,
        PremiseOperationsExecution.GeneralExecution.eventsTerm]
  | cons premise premises =>
    metta_call descent_checked
    metta_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites]
      with descent_checked
      unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm, continuationTerm, resultTerm, answerTerm, goalTerm,
        expansionTerm, schedulerExpansionTerm, taskTerm, encodeList, encodeOption, StructuralDescent.Scheduled.evaluate]

theorem descent_evaluate_steps_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Continuation environment (.steps depth bound type source limit) outer) :
    Evaluates state environment footprint (.steps depth bound type source limit) tail := by
  unfold Evaluates
  metta_call descent_checked
  metta_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites]
    with descent_checked
    unfolding [environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.GeneralExecution.providerTerm, continuationTerm, goalTerm,
      expansionTerm, schedulerExpansionTerm, taskTerm, encodeList, encodeOption, StructuralDescent.Scheduled.evaluate]

theorem descent_evaluate_query_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (relation : String) (arguments : List Pattern)
    (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.relationQuery relation arguments) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.relationQuery relation arguments) initial) tail := by
  unfold Evaluates
  rw [StructuralDescent.Scheduled.evaluate_relationQuery]
  descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites]
    unfolding [Query.start, PremiseOperationsExecution.GeneralExecution.queryStateTerm,
      PremiseOperationsExecution.GeneralExecution.queryTaskTerm, PremiseOperationsExecution.GeneralExecution.queryRequestTerm]

theorem descent_evaluate_forAll_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (collection parameter : String) (body : Premise)
    (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.forAll collection parameter body) initial) tail := by
  unfold Evaluates
  cases read : finiteCollection? context.bound.length initial collection with
  | none =>
    rw [StructuralDescent.Scheduled.evaluate_forAll_none collection parameter body tail read]
    descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
        descent_collection_returns state context.bound.length initial collection]
      unfolding [read, PremiseOperationsExecution.QuantifiedLocal.finiteCollectionOptionTerm]
  | some found =>
    obtain ⟨kind, elements⟩ := found
    rw [StructuralDescent.Scheduled.evaluate_forAll_some collection parameter body kind elements tail read]
    descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
        descent_collection_returns state context.bound.length initial collection]
      unfolding [read, PremiseOperationsExecution.QuantifiedLocal.finiteCollectionOptionTerm]

theorem descent_evaluate_congruence_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.congruence source target) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.congruence source target) initial) tail := by
  unfold Evaluates
  cases typed : sourceType? environment.language context.rule source with
  | none =>
    rw [StructuralDescent.Scheduled.evaluate_congruence_sort_none source target tail typed]
    descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
        descent_source_type_returns state environment.language context.rule source]
      unfolding [typed]
  | some type =>
    cases interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0 initial
        source with
    | none =>
      rw [StructuralDescent.Scheduled.evaluate_congruence_projection_none source target type tail typed interpreted]
      have sited : instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial source = none := interpreted
      descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
          descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
          descent_source_type_returns state environment.language context.rule source,
          descent_instantiate_returns state context.rule context.spec context.bound.length (.premise context.premiseIndex context.quantifierDepth 0) [] 0
            initial source]
        unfolding [typed, sited, ScopedInstantiationExecution.instantiationValues, Context.site,
          InferenceCettaWire.AuthoredRule.siteTerm, MatchAutomataBindingExecution.patternOptionTerm]
    | some actualSource =>
      rw [StructuralDescent.Scheduled.evaluate_congruence_some source target actualSource type tail typed interpreted]
      have sited : instantiateAt? context.rule context.spec context.bound.length
          (.premise context.premiseIndex context.quantifierDepth 0) [] 0 initial source = some actualSource := interpreted
      descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
          descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
          descent_source_type_returns state environment.language context.rule source,
          descent_instantiate_returns state context.rule context.spec context.bound.length (.premise context.premiseIndex context.quantifierDepth 0) [] 0
            initial source]
        unfolding [typed, sited, ScopedInstantiationExecution.instantiationValues, Context.site,
          InferenceCettaWire.AuthoredRule.siteTerm, MatchAutomataBindingExecution.patternOptionTerm,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

theorem descent_evaluate_scopedStep_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.scopedStep step) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.scopedStep step) initial) tail := by
  unfold Evaluates
  obtain ⟨binders, resultType, source, target⟩ := step
  cases interpreted : instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
      binders.length initial source with
  | none =>
    rw [StructuralDescent.Scheduled.evaluate_scopedStep_none _ tail interpreted]
    have sited : instantiateAt? context.rule context.spec context.bound.length
        (.premise context.premiseIndex context.quantifierDepth 0) [] binders.length initial source = none := interpreted
    descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state binders,
        descent_append_returns InferenceCettaWire.AuthoredRule.typeTerm state binders context.bound,
        descent_instantiate_returns state context.rule context.spec context.bound.length (.premise context.premiseIndex context.quantifierDepth 0) []
          binders.length initial source]
      unfolding [sited, ScopedInstantiationExecution.instantiationValues, Context.site,
        InferenceCettaWire.AuthoredRule.siteTerm, MatchAutomataBindingExecution.patternOptionTerm]
  | some actualSource =>
    rw [StructuralDescent.Scheduled.evaluate_scopedStep_some _ actualSource tail interpreted]
    have sited : instantiateAt? context.rule context.spec context.bound.length
        (.premise context.premiseIndex context.quantifierDepth 0) [] binders.length initial source =
          some actualSource := interpreted
    descent_eval [descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm state environment.language.rewrites,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state context.bound,
        descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state binders,
        descent_append_returns InferenceCettaWire.AuthoredRule.typeTerm state binders context.bound,
        descent_instantiate_returns state context.rule context.spec context.bound.length (.premise context.premiseIndex context.quantifierDepth 0) []
          binders.length initial source]
      unfolding [sited, ScopedInstantiationExecution.instantiationValues, Context.site,
        InferenceCettaWire.AuthoredRule.siteTerm, MatchAutomataBindingExecution.patternOptionTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
