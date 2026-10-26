import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentDeliver
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentEvaluateFreshness
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentEvaluateRoot

/-!
# Expanding tasks, ticking and running the descent machine

`gslt:descent:expand` expands each kind of task: it evaluates goals, delivers results, advances a
root or target match by one answer or one matcher tick, advances a query by one answer or one
query tick, and scans the children of a source. `gslt:descent:tick` expands the first task and
commits; `gslt:descent:run` ticks until its fuel is spent.

The free-type table every head receives is the environment's snapshot on a footprint. A run whose
initial state and provider stay within the footprint keeps every task within it, so each head
answers as the scheduled machine does, on every state the run reaches.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open StructuralDescent.Scheduled (Goal Result Task Obligation Continuation RootMatchFrame TargetMatchFrame)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

/-- **`gslt:descent:evaluate` is `evaluate`**, on every goal within the footprint. -/
@[metta_head "gslt:descent:evaluate"]
theorem descent_evaluate_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (goal : Goal) (tail : Continuation environment goal outer)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint goal) :
    Evaluates state environment footprint goal tail := by
  cases goal with
  | premise depth context premise initial =>
    cases premise with
    | relationQuery relation arguments =>
      exact descent_evaluate_query_returns state environment footprint depth context relation arguments initial tail
    | freshness condition =>
      exact descent_evaluate_freshness_returns state environment footprint depth context condition initial tail
    | forAll collection parameter body =>
      exact descent_evaluate_forAll_returns state environment footprint depth context collection parameter body
        initial tail
    | congruence source target =>
      exact descent_evaluate_congruence_returns state environment footprint depth context source target initial tail
    | scopedStep step =>
      exact descent_evaluate_scopedStep_returns state environment footprint depth context step initial tail
  | premises depth context premises initial =>
    exact descent_evaluate_premises_returns state environment footprint depth context premises initial tail
  | quantified depth context parameter body index elements initial =>
    exact descent_evaluate_quantified_returns state environment footprint depth context parameter body index elements
      initial tail covered
  | root depth bound type source index =>
    exact descent_evaluate_root_returns state environment footprint depth bound type source index tail covered
  | steps depth bound type source limit =>
    exact descent_evaluate_steps_returns state environment footprint depth bound type source limit tail

/-- A matcher answer as the MeTTa bodies read it. -/
theorem matcher_answer_term (answer : GeneralScopedMatchMachine.Answer) :
    RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answer =
      .application "ScopedMatcherAnswer" [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm answer.assignment,
        RuleInstantiationExecution.GeneralExecution.traceTerm answer.trace] := rfl

/-- The request a target match ticks, as the MeTTa body builds it. -/
theorem target_request_term {environment : Environment} (call : StructuralDescent.Scheduled.StepCall environment)
    (target : Pattern) :
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1, [],
          call.binders.length, call.initial, call.targetSchema, target⟩ =
      .application "ScopedMatcherRequest" [InferenceCettaWire.AuthoredRule.rewriteTerm call.context.rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm call.context.spec, .natural call.context.bound.length,
        .application "RulePremise" [.natural call.context.premiseIndex, .natural call.context.quantifierDepth,
          .natural 1],
        .symbol "LNil", .natural call.binders.length,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm call.initial,
        InferenceCettaWire.encodePattern call.targetSchema, InferenceCettaWire.encodePattern target] :=
  rfl

/-- A head that expands a task returns the scheduled machine's expansion. -/
def Expands (head : String) (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (task : Task environment outer)
    (expansion : Scheduler.Expansion (Task environment outer) (Result environment outer) Obligation) : Prop :=
  PureReturns descentLibrary.runtime [] state
    (apply head [environmentValue environment (environment.free.entriesOn footprint), encoded (taskTerm task)])
    state (encoded (encodeOption expansionTerm (some expansion)))

namespace Interpreted

theorem evaluate_premise_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (free : List (String × TypeExpr)) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (context : Context) (premise : Premise) (initial : Assignment)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.premise depth context premise initial) outer)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm (.premise depth context premise initial)),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer (.premise depth context premise initial) tail)))) := by
  cases premise with
  | relationQuery relation arguments =>
      exact evaluate_query_returns host environment matcher codec free profile depth context relation arguments initial tail view
  | freshness condition =>
      exact evaluate_freshness_returns host environment matcher codec free profile depth context condition initial tail view
  | forAll collection parameter body =>
      exact evaluate_forAll_returns host environment matcher codec free profile depth context collection parameter body initial tail view
  | congruence source target =>
      exact evaluate_congruence_returns host environment matcher codec free profile depth context source target initial tail view
  | scopedStep step =>
      exact evaluate_scopedStep_returns host environment matcher codec free profile depth context step initial tail view

theorem evaluate_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (goal : StructuralDescent.Scheduled.Goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment goal outer)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (roots : ∀ depth bound type source index, goal = .root depth bound type source index →
      ∀ rule spec, environment.language.rewrites[index]? = some rule → specification? environment index = some spec →
      admittedFor rule spec = true → checkOpenPatternWellSorted environment.language environment.free bound type source = true →
      requestReady ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint goal)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm goal), encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.evaluate environment outer goal tail)))) := by
  cases goal with
  | premise depth context premise initial =>
      exact evaluate_premise_returns host environment matcher codec (environment.free.entriesOn footprint) profile
        depth context premise initial tail view
  | premises depth context premises initial =>
      exact evaluate_premises_returns host environment matcher codec (environment.free.entriesOn footprint) profile
        depth context premises initial tail view
  | quantified depth context parameter body index elements initial =>
      exact evaluate_quantified_returns host environment matcher codec footprint profile
        depth context parameter body index elements initial tail covered view
  | root depth bound type source index =>
      exact evaluate_root_returns host environment matcher codec footprint profile depth bound type source index tail
        requestReady stateReady valueReady operations (roots depth bound type source index rfl) covered view
  | steps depth bound type source limit =>
      exact evaluate_steps_returns host environment matcher codec (environment.free.entriesOn footprint) profile
        depth bound type source limit tail view

#print axioms evaluate_returns

theorem query_returns (host : Effects.State) (environment : Environment) (matcher : MatchingExecution)
    (codec : RetainedMatchingWire.MatchingCodec matcher) (profile : Term)
    {outer : StructuralDescent.Scheduled.Goal} (depth : Nat) (request : Query.Request)
    (machine : Query.State environment request matcher) (cursor : Nat)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (expanded : ∀ current ∈ machine.agenda,
      PureReturns descentLibrary.runtime [] host (apply "gslt:premise:query-expand-in" [encoded profile,
        encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request),
        PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.taskValue codec current]) host
        (PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expansionValue codec (Query.expand environment request current))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:query"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec (.query depth request machine cursor tail))])
      host (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.expandQuery environment outer depth request machine cursor tail)))) := by
  have lookup := descent_row_returns (RetainedMatchingWire.queryAnswerTerm codec) host cursor machine.answers
  simp only [StructuralDescent.Scheduled.expandQuery]
  split
  · rename_i answer found
    have read := lookup
    simp only [found] at read
    descent_interpreted_eval [read]
      unfolding [found, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.resultTerm, RetainedMatchingWire.Scheduled.answerTerm,
        RetainedMatchingWire.queryStateTerm, RetainedMatchingWire.queryAnswerTerm, RetainedMatchingWire.eventTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, schedulerStateTerm, schedulerExpansionTerm,
        PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
        CompleteExecution.DescentCodec.goalTerm]
  · rename_i found
    have read := lookup
    simp only [found] at read
    cases agenda : machine.agenda with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte]
      have obligations := descent_query_obligations_returns host machine.unresolved
      descent_interpreted_eval [read, obligations]
        unfolding [found, agenda, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.queryStateTerm,
          RetainedMatchingWire.Scheduled.expansionTerm, schedulerStateTerm, schedulerExpansionTerm,
          PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm]
    | cons first rest =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      have next := expanded first (by rw [agenda]; exact List.mem_cons_self)
      have committed := descent_commit_returns host (RetainedMatchingWire.queryTaskTerm codec)
        (RetainedMatchingWire.queryAnswerTerm codec) PremiseOperationsExecution.GeneralExecution.queryObligationTerm
        (Query.expand environment request) machine
      descent_interpreted_eval [read, next, committed]
        unfolding [found, agenda, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.queryStateTerm,
          RetainedMatchingWire.Scheduled.expansionTerm, PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.taskValue, PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expansionValue,
          PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expansionTerm, schedulerStateTerm, schedulerExpansionTerm,
          PremiseOperationsExecution.GeneralExecution.queryRequestTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
          Query.tick]

theorem continue_root_answer_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : RuleBinding.admittedFor rule spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free bound type source)
    (answer : matcher.Answer)
    (valid : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer))
    (captures : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames (matcher.assignment answer), name ∈ footprint)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (StructuralDescent.Scheduled.Interpreted.Task matcher environment outer))
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:continue-root-answer"
      [encoded profile, number depth,
        encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
        encoded (InferenceCettaWire.AuthoredRule.typeTerm type), encoded (InferenceCettaWire.encodePattern source), number index,
        encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule), encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
        encoded (RetainedMatchingWire.matcherAnswerTerm codec answer),
        encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail),
        encoded (encodeList (RetainedMatchingWire.Scheduled.taskTerm codec) next)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.continueRootAnswer environment outer depth bound type source index rule spec
          declared specified admitted sorted answer valid tail next)))) := by
  let free := environment.free.entriesOn footprint
  have check := descent_check_assignment_returns host environment.language free bound rule spec
    (matcher.assignment answer)
  simp only [free, ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
    bound rule spec (matcher.assignment answer) footprint captures] at check
  simp only [StructuralDescent.Scheduled.continueRootAnswer]
  split
  · rename_i checked
    change ConditionalEquationExecution.checkAssignment environment.language environment.free bound rule spec
      (matcher.assignment answer) = true at checked
    descent_interpreted_eval [view, check]
      unfolding [checked, free, RetainedMatchingWire.matcherAnswerTerm,
        RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.continuationTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
        CompleteExecution.DescentCodec.goalTerm, CompleteExecution.DescentCodec.typesTerm,
        GeneralPremise.checkTypedAssignment, PremiseOperationsExecution.GeneralExecution.contextTerm,
        PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  · rename_i checked
    have failed : ConditionalEquationExecution.checkAssignment environment.language environment.free bound rule spec
        (matcher.assignment answer) = false := Bool.eq_false_iff.mpr checked
    descent_interpreted_eval [view, check]
      unfolding [failed, free, RetainedMatchingWire.matcherAnswerTerm,
        RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.continuationTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
        CompleteExecution.DescentCodec.goalTerm, CompleteExecution.DescentCodec.typesTerm,
        GeneralPremise.checkTypedAssignment, PremiseOperationsExecution.GeneralExecution.contextTerm,
        PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
        InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

theorem root_match_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (frame : StructuralDescent.Scheduled.RootMatchFrame environment outer matcher)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (ready : stateReady frame.state)
    (captures : ∀ answer ∈ matcher.answers frame.state,
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames (matcher.assignment answer), name ∈ footprint)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:root-match"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec (.rootMatch frame))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.expandRootMatch environment outer frame)))) := by
  have lookup := operations.answer host frame.state frame.cursor
  have finished := operations.complete host frame.state
  simp only [StructuralDescent.Scheduled.expandRootMatch]
  split
  · rename_i answer found
    have read := lookup
    simp only [found] at read
    have member := List.mem_of_getElem? found
    have valid := matcher.answers_sound frame.reachable member
    let later : StructuralDescent.Scheduled.Interpreted.Task matcher environment outer :=
      .rootMatch {frame with cursor := frame.cursor + 1}
    have continued := continue_root_answer_returns host environment matcher codec footprint profile frame.depth frame.bound
      frame.type frame.source frame.index frame.rule frame.spec frame.declared frame.specified frame.admitted frame.sorted
      answer valid (captures answer member) frame.tail [later] view
    descent_interpreted_eval [view, read, continued]
      unfolding [found, later, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.matcherAnswerTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
        PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
        InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  · rename_i found
    have read := lookup
    simp only [found] at read
    cases completed : matcher.complete frame.state with
    | true =>
      simp only [↓reduceIte]
      descent_interpreted_eval [view, read, finished]
        unfolding [found, completed, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.expansionTerm,
          schedulerExpansionTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
          PremiseOperationsExecution.GeneralExecution.providerTerm, InferenceCettaWire.AuthoredRule.rewriteTerm]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      let request : GeneralScopedMatchMachine.Request :=
        ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩
      have stepped := operations.tick host request frame.state ready
      simp only [request, root_request_term] at stepped
      have size := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host frame.bound
      descent_interpreted_eval [view, read, finished, stepped, size]
        unfolding [found, completed, request, RetainedMatchingWire.Scheduled.taskTerm,
          RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
          RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
          PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
          InferenceCettaWire.AuthoredRule.rewriteTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

theorem target_match_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (footprint : List String) (profile : Term) {outer : StructuralDescent.Scheduled.Goal}
    (frame : StructuralDescent.Scheduled.TargetMatchFrame environment outer matcher)
    (requestReady : GeneralScopedMatchMachine.Request → Prop) (stateReady : matcher.State → Prop) (valueReady : Pattern → Prop)
    (operations : RetainedMatchingWire.MatchingOperations descentLibrary.runtime matcher codec profile requestReady stateReady valueReady)
    (ready : stateReady frame.state)
    (captures : ∀ answer ∈ matcher.answers frame.state,
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames (matcher.assignment answer), name ∈ footprint)
    (view : PureReturns descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:target-match"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec (.targetMatch frame))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.expandTargetMatch environment outer frame)))) := by
  have lookup := operations.answer host frame.state frame.cursor
  have finished := operations.complete host frame.state
  simp only [StructuralDescent.Scheduled.expandTargetMatch]
  split
  · rename_i answer found
    have read := lookup
    simp only [found] at read
    let free := environment.free.entriesOn footprint
    have check := descent_check_assignment_returns host environment.language free
      frame.call.context.bound frame.call.context.rule frame.call.context.spec (matcher.assignment answer)
    simp only [free, ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
      frame.call.context.bound frame.call.context.rule frame.call.context.spec (matcher.assignment answer) footprint
      (captures answer (List.mem_of_getElem? found))] at check
    have joined := descent_append_returns InferenceCettaWire.AuthoredRule.typeTerm host frame.call.binders frame.call.context.bound
    split
    · rename_i checked
      change ConditionalEquationExecution.checkAssignment environment.language environment.free
        frame.call.context.bound frame.call.context.rule frame.call.context.spec (matcher.assignment answer) = true at checked
      descent_interpreted_eval [view, read, check, joined]
        unfolding [found, checked, free, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.resultTerm,
          RetainedMatchingWire.Scheduled.answerTerm, RetainedMatchingWire.matcherAnswerTerm, RetainedMatchingWire.eventTerm,
          RetainedMatchingWire.stepCallTerm, RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
          CompleteExecution.DescentCodec.goalTerm, GeneralPremise.checkTypedAssignment,
          PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
          PremiseOperationsExecution.GeneralExecution.contextTerm,
          PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
    · rename_i checked
      have failed : ConditionalEquationExecution.checkAssignment environment.language environment.free
        frame.call.context.bound frame.call.context.rule frame.call.context.spec (matcher.assignment answer) = false :=
        Bool.eq_false_iff.mpr checked
      descent_interpreted_eval [view, read, check]
        unfolding [found, failed, free, RetainedMatchingWire.Scheduled.taskTerm,
          RetainedMatchingWire.matcherAnswerTerm, RetainedMatchingWire.stepCallTerm,
          RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm, GeneralPremise.checkTypedAssignment,
          PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
          PremiseOperationsExecution.GeneralExecution.contextTerm,
          PremiseOperationsExecution.DeclarationTyping.declarationsTerm, PremiseOperationsExecution.DeclarationTyping.freeContextTerm,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  · rename_i found
    have read := lookup
    simp only [found] at read
    cases completed : matcher.complete frame.state with
    | true =>
      simp only [↓reduceIte]
      descent_interpreted_eval [view, read, finished]
        unfolding [found, completed, RetainedMatchingWire.Scheduled.taskTerm,
          RetainedMatchingWire.stepCallTerm, RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
          PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
          PremiseOperationsExecution.GeneralExecution.contextTerm]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      let request : GeneralScopedMatchMachine.Request :=
        ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
          frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial, frame.call.targetSchema, frame.target⟩
      have stepped := operations.tick host request frame.state ready
      have ambient := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host frame.call.context.bound
      have localSize := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm host frame.call.binders
      descent_interpreted_eval [view, read, finished, stepped, ambient, localSize]
        unfolding [found, completed, request, RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.stepCallTerm,
          RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm,
          RuleInstantiationExecution.GeneralExecution.matcherRequestTerm, GeneralPremise.Context.site,
          InferenceCettaWire.AuthoredRule.siteTerm, PremiseOperationsExecution.GeneralExecution.contextTerm,
          PremiseOperationsExecution.GeneralExecution.environmentTerm, PremiseOperationsExecution.GeneralExecution.providerTerm,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

#print axioms target_match_returns

/-- The delegated descentLibrary.runtime operation selected by a retained task. Scanning rule indices is inline. -/
def branchCall? {matcher : MatchingExecution} (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) {environment : Environment} {outer : StructuralDescent.Scheduled.Goal}
    (task : StructuralDescent.Scheduled.Interpreted.Task matcher environment outer) : Option Atom :=
  match task with
  | .evaluate goal tail => some (apply "gslt:descent:evaluate" [encoded profile,
      encoded (CompleteExecution.DescentCodec.goalTerm goal),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)])
  | .deliver result tail => some (apply "gslt:descent:deliver" [encoded profile,
      encoded (RetainedMatchingWire.Scheduled.resultTerm codec result),
      encoded (RetainedMatchingWire.Scheduled.continuationTerm codec tail)])
  | .query .. => some (apply "gslt:descent:query"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec task)])
  | .rootMatch .. => some (apply "gslt:descent:root-match"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec task)])
  | .targetMatch .. => some (apply "gslt:descent:target-match"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec task)])
  | .scanChildren .. => none

/-- Realizing the selected lower operation realizes descentLibrary.runtime task expansion; scanning is proved directly. -/
theorem expand_of_branch_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) (outer : StructuralDescent.Scheduled.Goal)
    (task : StructuralDescent.Scheduled.Interpreted.Task matcher environment outer)
    (realized : ∀ call ∈ branchCall? codec profile task,
      PureReturns descentLibrary.runtime [] host call host
        (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
          (some (StructuralDescent.Scheduled.expand environment outer task))))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:expand"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec task)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (StructuralDescent.Scheduled.expand environment outer task)))) := by
  cases task with
  | evaluate goal tail =>
    have branch := realized _ rfl
    descent_interpreted_eval [branch] unfolding [RetainedMatchingWire.Scheduled.taskTerm]
  | deliver result tail =>
    have branch := realized _ rfl
    descent_interpreted_eval [branch] unfolding [RetainedMatchingWire.Scheduled.taskTerm]
  | query depth request search cursor tail =>
    have branch := realized _ rfl
    descent_interpreted_eval [branch] unfolding [RetainedMatchingWire.Scheduled.taskTerm]
  | rootMatch frame =>
    have branch := realized _ rfl
    descent_interpreted_eval [branch] unfolding [RetainedMatchingWire.Scheduled.taskTerm]
  | targetMatch frame =>
    have branch := realized _ rfl
    descent_interpreted_eval [branch] unfolding [RetainedMatchingWire.Scheduled.taskTerm]
  | scanChildren depth bound type source limit cursor tail =>
    by_cases earlier : cursor < limit
    · simp only [StructuralDescent.Scheduled.expand, dif_pos earlier]
      descent_interpreted_eval unfolding [earlier, RetainedMatchingWire.Scheduled.taskTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, RetainedMatchingWire.Scheduled.resultTerm,
        RetainedMatchingWire.Scheduled.continuationTerm, CompleteExecution.DescentCodec.goalTerm,
        schedulerExpansionTerm]
    · simp only [StructuralDescent.Scheduled.expand, dif_neg earlier]
      descent_interpreted_eval unfolding [earlier, RetainedMatchingWire.Scheduled.taskTerm,
        RetainedMatchingWire.Scheduled.expansionTerm, schedulerExpansionTerm]

/-- The descentLibrary.runtime scheduler tick composes any realized interpreted task expansion. -/
theorem tick_of_expand_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) (goal : StructuralDescent.Scheduled.Goal)
    (search : StructuralDescent.Scheduled.State environment goal matcher)
    (expands : ∀ first ∈ search.agenda.head?,
      PureReturns descentLibrary.runtime [] host (apply "gslt:descent:expand"
        [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec first)]) host
        (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
          (some (StructuralDescent.Scheduled.expand environment goal first))))) :
    PureReturns descentLibrary.runtime [] host (apply "gslt:descent:tick"
      [encoded profile, encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm codec
        (StructuralDescent.Scheduled.tick environment goal search))) := by
  obtain ⟨agenda, answers, unresolved, work⟩ := search
  cases agenda with
  | nil =>
    descent_interpreted_eval unfolding [RetainedMatchingWire.Scheduled.stateTerm, schedulerStateTerm,
      encodeList, StructuralDescent.Scheduled.tick, Scheduler.tick]
  | cons first rest =>
    have expanded := expands first rfl
    have committed := descent_commit_returns host (RetainedMatchingWire.Scheduled.taskTerm codec)
      (RetainedMatchingWire.Scheduled.resultTerm codec) CompleteExecution.DescentCodec.obligationTerm
      (StructuralDescent.Scheduled.expand environment goal) ⟨first :: rest, answers, unresolved, work⟩
    descent_interpreted_eval [expanded, committed] unfolding [RetainedMatchingWire.Scheduled.stateTerm,
      RetainedMatchingWire.Scheduled.expansionTerm, schedulerStateTerm, schedulerExpansionTerm,
      encodeList, encodeOption, StructuralDescent.Scheduled.tick]

/-- Native execution preserves the retained scheduler state for any proved expansion invariant. -/
theorem run_of_invariant_returns (host : Effects.State) (environment : Environment)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : Term) (goal : StructuralDescent.Scheduled.Goal)
    (invariant : StructuralDescent.Scheduled.State environment goal matcher → Prop)
    (preserved : ∀ search, invariant search → invariant (StructuralDescent.Scheduled.tick environment goal search))
    (expands : ∀ search, invariant search → ∀ first ∈ search.agenda.head?,
      PureReturns descentLibrary.runtime [] host (apply "gslt:descent:expand"
        [encoded profile, encoded (RetainedMatchingWire.Scheduled.taskTerm codec first)]) host
        (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
          (some (StructuralDescent.Scheduled.expand environment goal first))))) :
    ∀ (fuel : Nat) (search : StructuralDescent.Scheduled.State environment goal matcher), invariant search →
      PureReturns descentLibrary.runtime [] host (apply "gslt:descent:run"
        [encoded profile, number fuel, encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) host
        (encoded (RetainedMatchingWire.Scheduled.stateTerm codec
          (StructuralDescent.Scheduled.run environment goal fuel search)))
  | 0, search, _ => by
    descent_interpreted_eval unfolding [StructuralDescent.Scheduled.run, Scheduler.run]
  | fuel + 1, search, holds => by
    have ticked := tick_of_expand_returns host environment matcher codec profile goal search (expands search holds)
    have continued := run_of_invariant_returns host environment matcher codec profile goal invariant preserved expands fuel
      (StructuralDescent.Scheduled.tick environment goal search) (preserved search holds)
    descent_interpreted_eval [ticked, continued] unfolding [StructuralDescent.Scheduled.run, Scheduler.run,
      StructuralDescent.Scheduled.tick]

end Interpreted

/-- **`gslt:descent:continue-root-answer` is `continueRootAnswer`.**
Any certified matcher backend may enter here after it has produced one valid
root answer; typing, premise replay and reduct construction remain shared. -/
@[metta_head "gslt:descent:continue-root-answer"]
theorem descent_continue_root_answer_returns (state : State)
    (environment : Environment) (footprint : List String) {outer : Goal}
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      environment.language environment.free bound type source)
    (answer : GeneralScopedMatchMachine.Answer)
    (valid : answer.Valid ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
    (captured : assignmentFreeWithin footprint answer.assignment)
    (tail : Continuation environment (.root (depth + 1) bound type source index) outer)
    (next : List (Task environment outer)) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:descent:continue-root-answer"
        [environmentValue environment (environment.free.entriesOn footprint), number depth,
          encoded (PremiseOperationsExecution.GeneralExecution.Base.typesTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm type),
          encoded (InferenceCettaWire.encodePattern source), number index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answer),
          encoded (continuationTerm tail), encoded (encodeList taskTerm next)])
      state (encoded (encodeOption expansionTerm (some
        (StructuralDescent.Scheduled.continueRootAnswer environment outer depth bound type
          source index rule spec declared specified admitted sorted answer valid tail next)))) := by
  simpa only [environmentValue, RetainedMatchingWire.ordinary_matcherAnswer,
    RetainedMatchingWire.Scheduled.ordinary_continuation, Interpreted.ordinary_task_terms,
    Interpreted.ordinary_expansion_terms] using
    Interpreted.continue_root_answer_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec footprint
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))
      depth bound type source index rule spec declared specified admitted sorted answer valid
      (ConditionalEquationExecution.assignment_free_names_covered footprint _ captured) tail next
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint))

/-- **`gslt:descent:root-match` is `expandRootMatch`.** -/
@[metta_head "gslt:descent:root-match"]
theorem descent_root_match_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (frame : RootMatchFrame environment outer)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint) :
    Expands "gslt:descent:root-match" state environment footprint (.rootMatch frame)
      (StructuralDescent.Scheduled.expandRootMatch environment outer frame) := by
  unfold Expands
  simpa only [environmentValue, Interpreted.ordinary_task_terms,
    Interpreted.ordinary_expansion_terms] using
    (Interpreted.root_match_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec footprint
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))
      frame (fun _ => True) (fun _ => True) (fun _ => True)
      (Interpreted.ordinary_matching_operations environment (environment.free.entriesOn footprint)) True.intro
      (fun answer member => ConditionalEquationExecution.assignment_free_names_covered footprint _
        (GeneralScopedMatchMachine.matcher_answer_free_within _ frame.state frame.reachable answer member
          footprint (by intro entry member; cases member) source))
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint)))

/-- **`gslt:descent:target-match` is `expandTargetMatch`.** -/
@[metta_head "gslt:descent:target-match"]
theorem descent_target_match_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (frame : TargetMatchFrame environment outer)
    (call : Execution.stepCallFreeWithin footprint frame.call)
    (target : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint) :
    Expands "gslt:descent:target-match" state environment footprint (.targetMatch frame)
      (StructuralDescent.Scheduled.expandTargetMatch environment outer frame) := by
  unfold Expands
  simpa only [environmentValue, Interpreted.ordinary_task_terms,
    Interpreted.ordinary_expansion_terms] using
    (Interpreted.target_match_returns state environment MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec footprint
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))
      frame (fun _ => True) (fun _ => True) (fun _ => True)
      (Interpreted.ordinary_matching_operations environment (environment.free.entriesOn footprint)) True.intro
      (fun answer member => ConditionalEquationExecution.assignment_free_names_covered footprint _
        (GeneralScopedMatchMachine.matcher_answer_free_within _ frame.state frame.reachable answer member
          footprint call.2.1 target))
      (Interpreted.ordinary_environment_returns state environment (environment.free.entriesOn footprint)))

/-- **`gslt:descent:query` is `expandQuery`**, for a finite provider within the footprint. -/
@[metta_head "gslt:descent:query"]
theorem descent_query_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    {outer : Goal} (depth : Nat) (request : Query.Request) (queryState : Query.State environment request)
    (cursor : Nat)
    (tail : Continuation environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (covered : Query.stateFreeWithin footprint environment request queryState) :
    Expands "gslt:descent:query" state environment footprint (.query depth request queryState cursor tail)
      (StructuralDescent.Scheduled.expandQuery environment outer depth request queryState cursor tail) := by
  unfold Expands
  have row := descent_row_returns PremiseOperationsExecution.GeneralExecution.QueryExecution.queryAnswerTerm state
    cursor queryState.answers
  cases found : queryState.answers[cursor]? with
  | some answer =>
    rw [StructuralDescent.Scheduled.expandQuery_found tail found]
    descent_eval_bound [row]
      unfolding [found, PremiseOperationsExecution.GeneralExecution.queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm,
        PremiseOperationsExecution.GeneralExecution.QueryExecution.queryAnswerTerm,
        PremiseOperationsExecution.GeneralExecution.queryRequestTerm,
        PremiseOperationsExecution.GeneralExecution.eventTerm]
  | none =>
    rw [StructuralDescent.Scheduled.expandQuery_missing tail found]
    cases agenda : queryState.agenda with
    | nil =>
      have obligations := descent_query_obligations_returns state queryState.unresolved
      simp only [List.isEmpty_nil, ↓reduceIte]
      descent_eval_bound [row, obligations]
        unfolding [found, agenda, PremiseOperationsExecution.GeneralExecution.queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          PremiseOperationsExecution.GeneralExecution.queryRequestTerm]
    | cons first rest =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      have expanded := descent_query_expand_returns state environment finiteProvider request first footprint provider
        (by
          intro frame same
          have covering := covered.1 first (by rw [agenda]; exact List.mem_cons_self)
          subst same
          exact ConditionalEquationExecution.assignment_free_names_covered footprint _ covering.1)
      have committed := descent_commit_returns state PremiseOperationsExecution.GeneralExecution.queryTaskTerm
        PremiseOperationsExecution.GeneralExecution.QueryExecution.queryAnswerTerm
        PremiseOperationsExecution.GeneralExecution.queryObligationTerm (Query.expand environment request) queryState
      descent_eval_bound [row, expanded, committed]
        unfolding [found, agenda, PremiseOperationsExecution.GeneralExecution.queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          PremiseOperationsExecution.GeneralExecution.queryRequestTerm,
          PremiseOperationsExecution.GeneralExecution.QueryExecution.queryExpansionTerm, Query.tick]

/-- **`gslt:descent:expand` is `expand`**, on every task within the footprint, for a finite provider
within it. -/
@[metta_head "gslt:descent:expand"]
theorem descent_expand_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    {outer : Goal} (task : Task environment outer)
    (covered : StructuralDescent.Scheduled.taskFreeWithin footprint task) :
    Expands "gslt:descent:expand" state environment footprint task
      (StructuralDescent.Scheduled.expand environment outer task) := by
  unfold Expands
  cases task with
  | evaluate goal tail =>
    have evaluated := descent_evaluate_returns state environment footprint goal tail covered.1
    unfold Evaluates at evaluated
    descent_eval [evaluated] unfolding [StructuralDescent.Scheduled.expand]
  | deliver result tail =>
    have delivered := descent_deliver_returns state environment footprint result tail covered.1
    unfold Delivers at delivered
    descent_eval [delivered] unfolding [StructuralDescent.Scheduled.expand]
  | query depth request queryState cursor tail =>
    have queried := descent_query_returns state environment finiteProvider footprint provider depth request queryState
      cursor tail covered.2.1
    unfold Expands at queried
    descent_eval [queried] unfolding [StructuralDescent.Scheduled.expand]
  | rootMatch frame =>
    have matched := descent_root_match_returns state environment footprint frame covered.1
    unfold Expands at matched
    descent_eval [matched] unfolding [StructuralDescent.Scheduled.expand]
  | targetMatch frame =>
    have matched := descent_target_match_returns state environment footprint frame covered.1 covered.2.2.2.1
    unfold Expands at matched
    descent_eval [matched] unfolding [StructuralDescent.Scheduled.expand]
  | scanChildren depth bound type source limit cursor tail =>
    by_cases earlier : cursor < limit
    · simp only [StructuralDescent.Scheduled.expand, dif_pos earlier]
      descent_eval_bound [] unfolding [earlier]
    · simp only [StructuralDescent.Scheduled.expand, dif_neg earlier]
      descent_eval_bound [] unfolding [earlier]

/-- `gslt:descent:tick` is the scheduled machine's tick, given what `gslt:descent:expand` returns on
the first task. -/
theorem descent_tick_of_expand (state : State) (environment : Environment) (free : List (String × TypeExpr))
    (goal : Goal) (search : StructuralDescent.Scheduled.State environment goal)
    (expands : ∀ first ∈ search.agenda.head?,
      PureReturns descentLibrary.runtime [] state
        (apply "gslt:descent:expand" [environmentValue environment free, encoded (taskTerm first)]) state
        (encoded (encodeOption expansionTerm (some (StructuralDescent.Scheduled.expand environment goal first))))) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:descent:tick" [environmentValue environment free, descentStateValue search]) state
      (descentStateValue (StructuralDescent.Scheduled.tick environment goal search)) := by
  simpa only [environmentValue, descentStateValue, RetainedMatchingWire.Scheduled.ordinary_state,
    Interpreted.ordinary_task_terms, Interpreted.ordinary_expansion_terms] using
    Interpreted.tick_of_expand_returns state environment MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free) goal search
      (fun first member => by
        simpa only [Interpreted.ordinary_task_terms,
          Interpreted.ordinary_expansion_terms] using expands first member)

/-- `gslt:descent:run` is the scheduled machine's run, from any state of an invariant that ticks
preserve and under which `gslt:descent:expand` returns the expansion of the first task. -/
theorem descent_run_of_invariant (state : State) (environment : Environment) (free : List (String × TypeExpr))
    (goal : Goal) (invariant : StructuralDescent.Scheduled.State environment goal → Prop)
    (preserved : ∀ search, invariant search → invariant (StructuralDescent.Scheduled.tick environment goal search))
    (expands : ∀ search, invariant search → ∀ first ∈ search.agenda.head?,
      PureReturns descentLibrary.runtime [] state
        (apply "gslt:descent:expand" [environmentValue environment free, encoded (taskTerm first)]) state
        (encoded (encodeOption expansionTerm (some (StructuralDescent.Scheduled.expand environment goal first))))) :
    ∀ (fuel : Nat) (search : StructuralDescent.Scheduled.State environment goal), invariant search →
      PureReturns descentLibrary.runtime [] state
        (apply "gslt:descent:run" [environmentValue environment free, number fuel, descentStateValue search]) state
        (descentStateValue (StructuralDescent.Scheduled.run environment goal fuel search)) := by
  intro fuel search holds
  simpa only [environmentValue, descentStateValue, RetainedMatchingWire.Scheduled.ordinary_state] using
    Interpreted.run_of_invariant_returns state environment MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free) goal invariant preserved
      (fun search valid first member => by
        simpa only [Interpreted.ordinary_task_terms,
          Interpreted.ordinary_expansion_terms] using expands search valid first member)
      fuel search holds

/-- **`gslt:descent:tick` is the scheduled machine's tick**, on every state within the footprint. -/
@[metta_head "gslt:descent:tick"]
theorem descent_tick_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (goal : Goal) (search : StructuralDescent.Scheduled.State environment goal)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint environment goal search) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:descent:tick" [environmentValue environment (environment.free.entriesOn footprint),
        descentStateValue search]) state
      (descentStateValue (StructuralDescent.Scheduled.tick environment goal search)) :=
  descent_tick_of_expand state environment _ goal search fun first member =>
    descent_expand_returns state environment finiteProvider footprint provider first
      (covered.1 first (List.mem_of_mem_head? member))

/-- **`gslt:descent:run` is the scheduled machine's run**, from every state within the footprint. -/
@[metta_head "gslt:descent:run"]
theorem descent_run_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (goal : Goal) (fuel : Nat) (search : StructuralDescent.Scheduled.State environment goal)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint environment goal search) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:descent:run" [environmentValue environment (environment.free.entriesOn footprint), number fuel,
        descentStateValue search]) state
      (descentStateValue (StructuralDescent.Scheduled.run environment goal fuel search)) := by
  have rows := provider_coverage_mono _ footprint environment.provider provider
    (provider_covered_by_own_names environment.provider)
  have dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint environment finiteProvider
  exact descent_run_of_invariant state environment _ goal
    (StructuralDescent.Scheduled.stateFreeWithin footprint environment goal)
    (fun search holds => StructuralDescent.Scheduled.tick_free_within Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinary_preservesFreeNames footprint environment goal rows dynamic search
      holds)
    (fun search holds first member => descent_expand_returns state environment finiteProvider footprint provider first
      (holds.1 first (List.mem_of_mem_head? member)))
    fuel search covered

/-- **A run from the start of a goal within the footprint** is the scheduled machine's run. -/
theorem descent_run_from_start_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (goal : Goal) (initial : StructuralDescent.Scheduled.goalFreeWithin footprint goal) (fuel : Nat) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:descent:run" [environmentValue environment (environment.free.entriesOn footprint), number fuel,
        descentStateValue (StructuralDescent.Scheduled.start environment goal)]) state
      (descentStateValue (StructuralDescent.Scheduled.run environment goal fuel
        (StructuralDescent.Scheduled.start environment goal))) :=
  descent_run_returns state environment finiteProvider footprint provider goal fuel _
    (StructuralDescent.Scheduled.start_free_within footprint environment goal initial)

#print axioms Interpreted.evaluate_premise_returns
#print axioms Interpreted.evaluate_returns
#print axioms Interpreted.query_returns
#print axioms Interpreted.continue_root_answer_returns
#print axioms Interpreted.root_match_returns
#print axioms Interpreted.target_match_returns
#print axioms Interpreted.expand_of_branch_returns
#print axioms Interpreted.tick_of_expand_returns
#print axioms Interpreted.run_of_invariant_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
