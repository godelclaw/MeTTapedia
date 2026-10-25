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
  have snapshot := ConditionalEquationExecution.checkAssignment_snapshot
    environment.language environment.free bound rule spec answer.assignment footprint
    (ConditionalEquationExecution.assignment_free_names_covered footprint _ captured)
  have check := descent_check_assignment_returns state environment.language
    (environment.free.entriesOn footprint) bound rule spec answer.assignment
  by_cases checked : checkTypedAssignment environment
      ⟨index, rule, spec, bound, 0, 0⟩ answer.assignment = true
  · rw [show StructuralDescent.Scheduled.continueRootAnswer environment outer depth bound type
        source index rule spec declared specified admitted sorted answer valid tail next =
        { tasks := .evaluate (.premises depth ⟨index, rule, spec, bound, 0, 0⟩
            rule.premises answer.assignment)
            (.rootBody depth bound type source index rule spec declared specified admitted sorted
              answer.trace answer.assignment
              (by simpa [GeneralScopedMatchMachine.Answer.Valid, MatchingExecution.ordinary,
                ordinaryInterpretation] using valid)
              (checkTypedAssignment_sound checked) tail) :: next } by
      simp only [StructuralDescent.Scheduled.continueRootAnswer, checked, ↓reduceDIte]]
    have answered : ConditionalEquationExecution.checkAssignment environment.language
        (FreeTypeContext.ofList (environment.free.entriesOn footprint)) bound rule spec
        answer.assignment = true := by rw [snapshot]; exact checked
    descent_eval_bound [check]
      unfolding [answered, matcher_answer_term,
        InferenceCettaWire.AuthoredRule.rewriteTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  · have checkedFalse : checkTypedAssignment environment
        ⟨index, rule, spec, bound, 0, 0⟩ answer.assignment = false :=
      Bool.eq_false_iff.mpr checked
    rw [show StructuralDescent.Scheduled.continueRootAnswer environment outer depth bound type
        source index rule spec declared specified admitted sorted answer valid tail next =
        { tasks := next } by
      simp only [StructuralDescent.Scheduled.continueRootAnswer, checkedFalse,
        Bool.false_eq_true, ↓reduceDIte]]
    have answered : ConditionalEquationExecution.checkAssignment environment.language
        (FreeTypeContext.ofList (environment.free.entriesOn footprint)) bound rule spec
        answer.assignment = false := by rw [snapshot]; exact checkedFalse
    descent_eval_bound [check]
      unfolding [answered, matcher_answer_term,
        InferenceCettaWire.AuthoredRule.rewriteTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

/-- **`gslt:descent:root-match` is `expandRootMatch`.** -/
@[metta_head "gslt:descent:root-match"]
theorem descent_root_match_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (frame : RootMatchFrame environment outer)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint) :
    Expands "gslt:descent:root-match" state environment footprint (.rootMatch frame)
      (StructuralDescent.Scheduled.expandRootMatch environment outer frame) := by
  unfold Expands
  have row := descent_row_returns RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm state frame.cursor
    frame.state.answers
  cases found : frame.state.answers[frame.cursor]? with
  | none =>
    rw [StructuralDescent.Scheduled.expandRootMatch_missing frame found]
    have completeFact := descent_matcher_complete_returns state frame.state
    cases complete : GeneralScopedMatchMachine.complete frame.state with
    | true =>
      simp only [↓reduceIte]
      descent_eval [row, completeFact]
        unfolding [found, complete, RuleInstantiationExecution.GeneralExecution.matcherStateTerm,
          InferenceCettaWire.AuthoredRule.rewriteTerm]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have bounds := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state frame.bound
      have ticked := descent_matcher_tick_returns state
        ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩ frame.state
      descent_eval_bound [row, completeFact, bounds, ticked]
        unfolding [found, complete, RuleInstantiationExecution.GeneralExecution.matcherStateTerm,
          InferenceCettaWire.AuthoredRule.rewriteTerm, root_request_term,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  | some answer =>
    rw [StructuralDescent.Scheduled.expandRootMatch_found frame found]
    have captured := GeneralScopedMatchMachine.matcher_answer_free_within _ frame.state frame.reachable answer (List.mem_of_getElem? found)
      footprint (by intro entry member; cases member) source
    have valid := GeneralScopedMatchMachine.answers_sound frame.reachable
      (List.mem_of_getElem? found)
    let later : Task environment outer := .rootMatch { frame with cursor := frame.cursor + 1 }
    have continued := descent_continue_root_answer_returns state environment footprint
      frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
      frame.declared frame.specified frame.admitted frame.sorted answer valid captured
      frame.tail [later]
    descent_eval_bound [row, continued]
      unfolding [found, later, RuleInstantiationExecution.GeneralExecution.matcherStateTerm,
        matcher_answer_term, InferenceCettaWire.AuthoredRule.rewriteTerm,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

/-- **`gslt:descent:target-match` is `expandTargetMatch`.** -/
@[metta_head "gslt:descent:target-match"]
theorem descent_target_match_returns (state : State) (environment : Environment) (footprint : List String)
    {outer : Goal} (frame : TargetMatchFrame environment outer)
    (call : Execution.stepCallFreeWithin footprint frame.call)
    (target : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint) :
    Expands "gslt:descent:target-match" state environment footprint (.targetMatch frame)
      (StructuralDescent.Scheduled.expandTargetMatch environment outer frame) := by
  unfold Expands
  have row := descent_row_returns RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm state frame.cursor
    frame.state.answers
  cases found : frame.state.answers[frame.cursor]? with
  | none =>
    rw [StructuralDescent.Scheduled.expandTargetMatch_missing frame found]
    have completeFact := descent_matcher_complete_returns state frame.state
    cases complete : GeneralScopedMatchMachine.complete frame.state with
    | true =>
      simp only [↓reduceIte]
      descent_eval [row, completeFact]
        unfolding [found, complete, RuleInstantiationExecution.GeneralExecution.matcherStateTerm]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have bounds := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state frame.call.context.bound
      have binders := descent_length_returns InferenceCettaWire.AuthoredRule.typeTerm state frame.call.binders
      have ticked := descent_matcher_tick_returns state
        ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
          frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial, frame.call.targetSchema,
          frame.target⟩ frame.state
      descent_eval_bound [row, completeFact, bounds, binders, ticked]
        unfolding [found, complete, RuleInstantiationExecution.GeneralExecution.matcherStateTerm,
          target_request_term, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
  | some answer =>
    rw [StructuralDescent.Scheduled.expandTargetMatch_found frame found]
    have captured := GeneralScopedMatchMachine.matcher_answer_free_within _ frame.state frame.reachable answer (List.mem_of_getElem? found)
      footprint call.2.1 target
    have snapshot := ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free
      frame.call.context.bound frame.call.context.rule frame.call.context.spec answer.assignment footprint
      (ConditionalEquationExecution.assignment_free_names_covered footprint _ captured)
    have check := descent_check_assignment_returns state environment.language (environment.free.entriesOn footprint)
      frame.call.context.bound frame.call.context.rule frame.call.context.spec answer.assignment
    have joined := descent_append_returns InferenceCettaWire.AuthoredRule.typeTerm state frame.call.binders
      frame.call.context.bound
    by_cases checked : checkTypedAssignment environment frame.call.context answer.assignment = true
    · rw [dif_pos checked]
      have answered : ConditionalEquationExecution.checkAssignment environment.language
          (FreeTypeContext.ofList (environment.free.entriesOn footprint)) frame.call.context.bound
          frame.call.context.rule frame.call.context.spec answer.assignment = true := by
        rw [snapshot]
        exact checked
      descent_eval_bound [row, check, joined]
        unfolding [found, answered, RuleInstantiationExecution.GeneralExecution.matcherStateTerm, matcher_answer_term,
          PremiseOperationsExecution.GeneralExecution.eventTerm, PremiseOperationsExecution.GeneralExecution.Base.typesTerm]
    · rw [dif_neg checked]
      have answered : ConditionalEquationExecution.checkAssignment environment.language
          (FreeTypeContext.ofList (environment.free.entriesOn footprint)) frame.call.context.bound
          frame.call.context.rule frame.call.context.spec answer.assignment = false := by
        rw [snapshot]
        exact Bool.eq_false_iff.mpr checked
      descent_eval_bound [row, check]
        unfolding [found, answered, RuleInstantiationExecution.GeneralExecution.matcherStateTerm, matcher_answer_term,
          PremiseOperationsExecution.GeneralExecution.Base.typesTerm]

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
  obtain ⟨agenda, answers, unresolved, work⟩ := search
  metta_call descent_checked
  cases agenda with
  | nil =>
    metta_eval unfolding [descentStateValue, stateTerm, schedulerStateTerm, encodeList,
      StructuralDescent.Scheduled.tick, Scheduler.tick]
  | cons first rest =>
    metta_eval [expands first rfl,
        descent_commit_returns state taskTerm resultTerm obligationTerm
          (StructuralDescent.Scheduled.expand environment goal) ⟨first :: rest, answers, unresolved, work⟩]
      with descent_checked
      unfolding [descentStateValue, stateTerm, schedulerStateTerm, expansionTerm, encodeList, encodeOption,
        StructuralDescent.Scheduled.tick]

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
        (descentStateValue (StructuralDescent.Scheduled.run environment goal fuel search))
  | 0, search, _ => by
    metta_call descent_checked
    metta_eval unfolding [StructuralDescent.Scheduled.run, Scheduler.run]
  | fuel + 1, search, holds => by
    metta_call descent_checked
    metta_eval [descent_tick_of_expand state environment free goal search (expands search holds),
        descent_run_of_invariant state environment free goal invariant preserved expands fuel
          (StructuralDescent.Scheduled.tick environment goal search) (preserved search holds)]
      with descent_checked unfolding [StructuralDescent.Scheduled.run, Scheduler.run, StructuralDescent.Scheduled.tick]

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
    (fun search holds => StructuralDescent.Scheduled.tick_free_within footprint environment goal rows dynamic search
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

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
