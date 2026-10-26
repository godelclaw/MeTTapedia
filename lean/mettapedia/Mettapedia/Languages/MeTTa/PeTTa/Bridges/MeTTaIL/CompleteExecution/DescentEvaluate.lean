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
    `(tactic| (metta_call_in descentProof_checked using descentProof_agreement; metta_eval [$facts,*] with descentProof_checked in descentProof_agreement
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

namespace Interpreted

theorem evaluate_premises_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (premises : List Premise) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.premises depth context premises initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premises depth context premises initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer (.premises depth context premises initial) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  cases premises with
  | nil =>
    descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate, RetainedMatchingWire.eventsTerm]
  | cons premise premises =>
    descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate]

theorem evaluate_query_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (relation : String) (arguments : List Pattern) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.relationQuery relation arguments) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.relationQuery relation arguments) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.relationQuery relation arguments) initial) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluatePremise,
    PremiseOperationsExecution.GeneralExecution.queryRequestTerm, RetainedMatchingWire.queryStateTerm,
    RetainedMatchingWire.queryTaskTerm, Query.start, schedulerStateTerm]

theorem evaluate_steps_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.steps depth bound type source limit) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.steps depth bound type source limit)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer (.steps depth bound type source limit) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  descent_interpreted_eval [view, count] unfolding [StructuralDescent.Scheduled.evaluate]

theorem evaluate_forAll_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (collection parameter : String) (body : Premise) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.forAll collection parameter body) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.forAll collection parameter body) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.forAll collection parameter body) initial) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
  have collected := descent_collection_returns host context.bound.length initial collection
  simp only [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluatePremise]
  split
  · rename_i found
    have read := collected
    simp only [found] at read
    descent_interpreted_eval [view, count, bound, read]
      unfolding [PremiseOperationsExecution.QuantifiedLocal.finiteCollectionOptionTerm]
  · rename_i kind elements found
    have read := collected
    simp only [found] at read
    descent_interpreted_eval [view, count, bound, read]
      unfolding [PremiseOperationsExecution.QuantifiedLocal.finiteCollectionOptionTerm]

theorem evaluate_congruence_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.congruence source target) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.congruence source target) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.congruence source target) initial) tail)))) := by
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have typeRead := descent_source_type_returns host environment.language context.rule source
  simp only [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluatePremise]
  split
  · rename_i found
    have read := typeRead
    simp only [found] at read
    descent_interpreted_eval [view, count, read]
  · rename_i type found
    have read := typeRead
    simp only [found] at read
    have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
    have instantiated := descent_instantiate_returns host context.rule context.spec context.bound.length (context.site 0) [] 0 initial source
    split
    · rename_i projected
      have interpreted := instantiated
      simp only [projected] at interpreted
      descent_interpreted_eval [view, count, read, bound, interpreted]
        unfolding [Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm]
    · rename_i actualSource projected
      have interpreted := instantiated
      simp only [projected] at interpreted
      descent_interpreted_eval [view, count, read, bound, interpreted]
        unfolding [Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

theorem evaluate_scopedStep_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth context (.scopedStep step) initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context (.scopedStep step) initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer
          (.premise depth context (.scopedStep step) initial) tail)))) := by
  obtain ⟨binders, resultType, source, target⟩ := step
  have count := descent_length_returns InferenceCettaWire.AuthoredRule.rewriteTerm host environment.language.rewrites
  have bound := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host context.bound
  have localSize := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host binders
  have joined := descent_append_returns InferenceCettaWire.AuthoredRule.typeTerm host binders context.bound
  have instantiated := descent_instantiate_returns host context.rule context.spec context.bound.length (context.site 0) [] binders.length initial source
  simp only [StructuralDescent.Scheduled.evaluate, StructuralDescent.Scheduled.evaluatePremise]
  split
  · rename_i projected
    have interpreted := instantiated
    simp only [projected] at interpreted
    descent_interpreted_eval [view, count, bound, localSize, joined, interpreted]
      unfolding [Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm]
  · rename_i actualSource projected
    have interpreted := instantiated
    simp only [projected] at interpreted
    descent_interpreted_eval [view, count, bound, localSize, joined, interpreted]
      unfolding [Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
          MatchAutomataBindingExecution.patternOptionTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

end Interpreted

theorem descent_evaluate_premises_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (premises : List Premise) (initial : Assignment)
    (tail : Continuation environment (.premises depth context premises initial) outer) :
    Evaluates state environment footprint (.premises depth context premises initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_premises_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context premises initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_steps_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
    (tail : Continuation environment (.steps depth bound type source limit) outer) :
    Evaluates state environment footprint (.steps depth bound type source limit) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_steps_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth bound type source limit tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_query_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (relation : String) (arguments : List Pattern)
    (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.relationQuery relation arguments) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.relationQuery relation arguments) initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_query_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context relation arguments initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_forAll_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (collection parameter : String) (body : Premise)
    (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.forAll collection parameter body) initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_forAll_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context collection parameter body initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_congruence_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (source target : Pattern) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.congruence source target) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.congruence source target) initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_congruence_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context source target initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

theorem descent_evaluate_scopedStep_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (depth : Nat) (context : Context) (step : ScopedStepPremise) (initial : Assignment)
    (tail : Continuation environment (.premise depth context (.scopedStep step) initial) outer) :
    Evaluates state environment footprint (.premise depth context (.scopedStep step) initial) tail := by
  unfold Evaluates
  simpa only [environmentValue, RetainedMatchingWire.Scheduled.ordinary_continuation,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.evaluate_scopedStep_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec (environment.free.entriesOn footprint)
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
        (environment.free.entriesOn footprint)) depth context step initial tail
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

#print axioms Interpreted.evaluate_premises_returns
#print axioms descent_evaluate_premises_returns
#print axioms Interpreted.evaluate_steps_returns
#print axioms descent_evaluate_steps_returns
#print axioms Interpreted.evaluate_query_returns
#print axioms descent_evaluate_query_returns
#print axioms Interpreted.evaluate_forAll_returns
#print axioms descent_evaluate_forAll_returns
#print axioms Interpreted.evaluate_congruence_returns
#print axioms descent_evaluate_congruence_returns
#print axioms Interpreted.evaluate_scopedStep_returns
#print axioms descent_evaluate_scopedStep_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
