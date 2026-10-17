import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafEvaluation
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceScan
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory

/-!
# Independent leaf services through the retained first-success worker

A service job retains its complete evaluation endpoint and its previously
earned observations. Independent evaluator evidence determines its unique
reply. The constructed simulation realizes that reply through the existing
recursive worker, including its silent request entry and ordered publication.
A backward simulation reflects completion, and the stage composes with the
lossless configuration representation.

These are constructed service instances, not a replacement expression
evaluator. Casting and interpreted expression jobs require their additional
service correspondence. The native parent continuation is retained outside
the service job and needs its own callback/import/export connection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafService

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval FirstSuccessLeafEvaluation RecursiveTasks
open FirstSuccessRecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- An independently admitted service endpoint. Its budget belongs to the
source evaluator profile; the step interface has a separate work account. -/
structure Job where
  space : Space
  value : Atom
  expected : Atom
  bindings : Bindings
  evaluatorFuel : Nat
  earned : ResultSet
  leaf : LeafRel value expected

def Job.reply (job : Job) : ResultPair := (job.value, job.bindings)

def Job.pending (job : Job) : Configuration :=
  ⟨job.space, .work (.atom job.value job.expected job.bindings (job.evaluatorFuel + 1) []), [], job.earned⟩

def Job.ready (job : Job) : Configuration :=
  ⟨job.space, .returning [job.reply], [], job.earned⟩

def Job.finished (job : Job) : Configuration :=
  ⟨job.space, .returning [], [], job.earned ++ [job.reply]⟩

inductive State where
  | pending (job : Job)
  | yielded (job : Job)

/-- The coarse service publishes its independently determined reply, then
finishes with the complete retained configuration. -/
def serviceMachine : Machine State ResultPair Configuration Empty where
  step
    | .pending job => some (.publish [job.reply] (.yielded job))
    | .yielded job => some (.finish job.finished)

/-- Independent service semantics use evaluator derivations, not membership
in a recursive function's output. The complete reply is retained as an event. -/
inductive StepRel (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (scope : List String) :
    State → Transition State ResultPair Configuration Empty → Prop where
  | reply (job : Job) (result : ResultPair) :
      EvalAtomRawRel job.space dispatch live (protectedScope := scope) (typing := typing)
        job.value job.expected job.bindings result →
      StepRel dispatch live typing scope (.pending job) (.publish [result] (.yielded job))
  | finished (job : Job) :
      StepRel dispatch live typing scope (.yielded job) (.finish job.finished)

theorem service_step_sound (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (scope : List String) (state : State)
    (action : Transition State ResultPair Configuration Empty)
    (advanced : serviceMachine.step state = some action) : StepRel dispatch live typing scope state action := by
  cases state with
  | pending job =>
      cases advanced
      exact .reply job job.reply
        (leaf_evidence job.space dispatch live typing scope job.value job.expected job.bindings job.leaf)
  | yielded job => cases advanced; exact .finished job

theorem service_step_complete {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {scope : List String} {state : State}
    {action : Transition State ResultPair Configuration Empty}
    (earned : StepRel dispatch live typing scope state action) : serviceMachine.step state = some action := by
  cases earned with
  | reply job result evaluated =>
      have unique : result = job.reply :=
        BindingFrame.historicalResult_injective (leaf_unique job.leaf evaluated)
      subst result
      rfl
  | finished => rfl

theorem service_step_iff (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (scope : List String) (state : State)
    (action : Transition State ResultPair Configuration Empty) :
    serviceMachine.step state = some action ↔ StepRel dispatch live typing scope state action :=
  ⟨service_step_sound dispatch live typing scope state action, service_step_complete⟩

theorem pending_worker_step (source : HE.GroundedDispatch) (job : Job) :
    (machine source).step job.pending = some (.silent job.ready) := by
  have entered : FirstSuccessRecursiveStrategy.enter job.space source
      (.atom job.value job.expected job.bindings (job.evaluatorFuel + 1) []) =
        (.returning [job.reply], []) := by
    rcases (leaf_gate job.value job.expected).mp job.leaf with failed | passed
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, failed, if_true, Job.reply]
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, passed, if_true,
        ite_self, Job.reply]
  simp only [machine, next, Job.pending, entered, List.nil_append, Job.ready]

theorem ready_worker_step (source : HE.GroundedDispatch) (job : Job) :
    (machine source).step job.ready = some (.publish [job.reply] job.finished) := rfl

theorem finished_worker_step (source : HE.GroundedDispatch) (job : Job) :
    (machine source).step job.finished = some (.finish job.finished) := rfl

/-- The service's pending phase relates to both sides of the worker's silent
entry. The yielded phase retains the complete earned observation history. -/
def Relates : State → Configuration → Prop
  | .pending job, configuration => configuration = job.pending ∨ configuration = job.ready
  | .yielded job, configuration => configuration = job.finished

theorem service_forward (source : HE.GroundedDispatch) :
    CostSimulation serviceMachine (machine source) Relates 2 where
  silent := by
    intro state target after related stepped
    cases state <;> cases stepped
  publish := by
    intro state target events after related stepped
    cases state with
    | yielded job => cases stepped
    | pending job =>
        cases stepped
        rcases related with rfl | rfl
        · exact ⟨2, le_rfl, job.finished, by
            simp only [Machine.run, pending_worker_step, ready_worker_step,
              List.append_nil], rfl⟩
        · exact ⟨1, by omega, job.finished, by
            simp only [Machine.run, ready_worker_step, List.append_nil], rfl⟩
  finish := by
    intro state target verdict related stepped
    cases state with
    | pending job => cases stepped
    | yielded job =>
        cases stepped
        subst target
        exact ⟨1, by omega, by simp only [Machine.run, finished_worker_step]⟩
  fail := by
    intro state target events related stepped
    cases state <;> cases stepped
  call := by
    intro state target request saved related stepped
    nomatch request

theorem service_backward (source : HE.GroundedDispatch) :
    CostSimulation (machine source) serviceMachine (fun configuration state => Relates state configuration) 1 where
  silent := by
    intro target state after related stepped
    cases state with
    | yielded job => rw [related, finished_worker_step] at stepped; cases stepped
    | pending job =>
        rcases related with rfl | rfl
        · rw [pending_worker_step] at stepped
          cases stepped
          exact ⟨0, Nat.zero_le _, .pending job, rfl, Or.inr rfl⟩
        · rw [ready_worker_step] at stepped
          cases stepped
  publish := by
    intro target state events after related stepped
    cases state with
    | yielded job => rw [related, finished_worker_step] at stepped; cases stepped
    | pending job =>
        rcases related with rfl | rfl
        · rw [pending_worker_step] at stepped
          cases stepped
        · rw [ready_worker_step] at stepped
          cases stepped
          exact ⟨1, le_rfl, .yielded job, by simp only [Machine.run, serviceMachine,
            List.append_nil], rfl⟩
  finish := by
    intro target state verdict related stepped
    cases state with
    | yielded job =>
        rw [related, finished_worker_step] at stepped
        cases stepped
        exact ⟨1, le_rfl, rfl⟩
    | pending job =>
        rcases related with rfl | rfl
        · rw [pending_worker_step] at stepped
          cases stepped
        · rw [ready_worker_step] at stepped
          cases stepped
  fail := by
    intro target state events related stepped
    cases state with
    | yielded job => rw [related, finished_worker_step] at stepped; cases stepped
    | pending job =>
        rcases related with rfl | rfl
        · rw [pending_worker_step] at stepped
          cases stepped
        · rw [ready_worker_step] at stepped
          cases stepped
  call := by
    intro target state request saved related stepped
    nomatch request

def workerStage (source : HE.GroundedDispatch) : Stage serviceMachine (machine source) :=
  Stage.ofBackward Relates 2 (service_forward source) (service_backward source)

/-- Composition uses the constructed intermediate recursive configuration,
so residuals, final verdicts and ordered observations travel together. -/
def representedStage (source : HE.GroundedDispatch) : Stage serviceMachine (dataMachine source) :=
  (workerStage source).comp (representationStage source)

theorem represented_initial (source : HE.GroundedDispatch) (job : Job) :
    (representedStage source).related (.pending job) (RecursiveEncoding.configurationData job.pending) :=
  ⟨job.pending, Or.inl rfl, rfl⟩

theorem represented_service_reply (source : HE.GroundedDispatch) (job : Job) :
    (dataMachine source).observe 4 (RecursiveEncoding.configurationData job.pending) =
      ⟨[job.reply], .finished job.finished⟩ := by
  have observed := (representedStage source).observe_prefix 2 (represented_initial source job)
  have sourceFinished : serviceMachine.observe 2 (.pending job) =
      ⟨[job.reply], .finished job.finished⟩ := by
    simp only [Machine.observe, Machine.run, serviceMachine, List.append_nil, Outcome.status]
  rw [sourceFinished] at observed
  exact (observed.2 (by trivial)).symm

/-- Every final encoded observation of this service agrees with its unique
independent evaluator result, regardless of which sufficient budget finishes. -/
theorem completed_reply_evidence (source : HE.GroundedDispatch) (job : Job)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (scope : List String) (budget : Nat)
    (completed : ((dataMachine source).observe budget
      (RecursiveEncoding.configurationData job.pending)).status.Final) :
    (dataMachine source).observe budget (RecursiveEncoding.configurationData job.pending) =
      ⟨[job.reply], .finished job.finished⟩ ∧
    EvalAtomRawRel job.space dispatch live (protectedScope := scope) (typing := typing)
      job.value job.expected job.bindings job.reply := by
  have same := (representedStage source).final_eq (represented_initial source job)
    (fuel := 2) (fuel' := budget) (by trivial) completed
  refine ⟨?_, leaf_evidence job.space dispatch live typing scope job.value job.expected job.bindings job.leaf⟩
  simpa only [Machine.observe, Machine.run, serviceMachine, List.singleton_append,
    List.append_nil, Outcome.status] using same.symm

/-- An actual, independently earned leaf service reply is accepted only at
the currently retained native-controller endpoint. Its worker execution,
semantic derivation and ordered reply-history invariant are joined here;
endpoint decoding alone grants none of these guarantees. -/
theorem retained_evaluation_reply
    (configuration : NativeArgumentControl.Configuration) (argument : TypedApplyState)
    (prepared : NativeArgumentControl.Prepared) (rest : List NativeArgumentControl.Frame)
    (ticket : Nat) (pending : configuration.frames =
      .waiting (.evaluate argument prepared) ticket :: rest)
    (history : NativeArgumentControlHistory.HistoryInv configuration)
    (space : Space) (source : HE.GroundedDispatch) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (fuel charge : Nat)
    (leaf : LeafRel prepared.bound prepared.domain) :
    ∃ (job : Job) (after : NativeArgumentControl.Configuration),
      job.value = prepared.bound ∧ job.expected = prepared.domain ∧
      job.bindings = argument.env ∧
      NativeArgumentControl.DeliveryRel configuration
        ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
          .evaluated (evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)),
          charge⟩ after ∧
      NativeArgumentControlHistory.HistoryInv after ∧
      (dataMachine source).observe 4 (RecursiveEncoding.configurationData job.pending) =
        ⟨[job.reply], .finished job.finished⟩ ∧
      EvalAtomRawRel space dispatch live (typing := typing)
        prepared.bound prepared.domain argument.env job.reply := by
  let job : Job := ⟨space, prepared.bound, prepared.domain, argument.env, fuel, [], leaf⟩
  let reply : NativeArgumentControl.Reply :=
    ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
      .evaluated [(prepared.bound, argument.env)], charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared [(prepared.bound, argument.env)]) prepared]
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      [(prepared.bound, argument.env)] charge pending
  refine ⟨job, after, rfl, rfl, rfl, ?_,
    NativeArgumentControlHistory.delivery_preserves_history history accepted,
    represented_service_reply source job, ?_⟩
  · rw [source_leaf space source prepared.bound prepared.domain argument.env fuel leaf]
    exact (NativeArgumentControl.deliver_iff _ _ _).mp accepted
  · exact leaf_evidence space dispatch live typing [] _ _ _ leaf

section Controls

open FirstSuccessPreparedArguments NativeArgumentControl
open Spec.Type.Presentation

private def heldSyntax : Atom := .expression [.symbol "quote",
  .expression [.symbol "Pair", .var "unassigned", .var "unassigned"]]
private def substitution : TypeSubst := [("x", heldSyntax), ("T", Atom.atomType)]
private def argument : TypedApplyState :=
  ⟨.symbol "hold", [.var "x"], [.var "T"], 0, [], presentedBindings substitution⟩
private def policy : NativeArgumentControlPolicy.Policy := {dialect := .he}
private def prepared : Prepared := ⟨Atom.atomType, heldSyntax, policy⟩

theorem stored_unassigned_aliases_are_normal : substitution.Normal := by
  refine ⟨by decide, ?_⟩
  intro name value stored
  simp only [substitution, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at stored
  rcases stored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro candidate occurs
    have same : candidate = "unassigned" := by
      simpa only [heldSyntax, TypeSubst.typeVars, TypeSubst.typeVarsList,
        List.mem_append, List.mem_cons, List.mem_nil_iff, List.mem_singleton,
        or_self, or_false, false_or] using occurs
    subst candidate
    decide
  · intro candidate occurs
    simp [Atom.atomType, TypeSubst.typeVars] at occurs

theorem preparation_resolves_both_endpoints : prepareSource argument policy 6 = prepared := rfl

theorem preparation_has_independent_evidence : PreparationRel substitution argument policy prepared := by
  rw [← preparation_resolves_both_endpoints]
  exact preparation_sound stored_unassigned_aliases_are_normal argument policy 6 rfl
    (by decide) (by decide)

theorem original_and_resolved_arguments_are_distinct :
    original argument ≠ prepared.bound ∧ originalDomain argument ≠ prepared.domain := by decide

theorem saved_snapshot_keeps_the_original_domain :
    (selectedSnapshot argument prepared []).domain = .var "T" ∧
    (selectedSnapshot argument prepared []).original = .var "x" := ⟨rfl, rfl⟩

theorem original_variable_is_not_its_prepared_reply (space : Space) (source : HE.GroundedDispatch) :
    evalAtom space source (original argument) (originalDomain argument) argument.env 1 =
      [(.var "x", argument.env)] := rfl

theorem prepared_source_reply_keeps_nested_aliases (space : Space) (source : HE.GroundedDispatch) :
    evalAtom space source prepared.bound prepared.domain argument.env 1 =
      [(heldSyntax, argument.env)] := rfl

private theorem held_leaf : LeafRel heldSyntax Atom.atomType :=
  Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩

private def heldJob (earned : ResultSet) : Job :=
  ⟨Space.empty, heldSyntax, Atom.atomType, argument.env, 0, earned, held_leaf⟩

theorem represented_reply_retains_duplicated_prior_occurrences (source : HE.GroundedDispatch) :
    (dataMachine source).observe 4
      (RecursiveEncoding.configurationData (heldJob [(heldSyntax, argument.env),
        (heldSyntax, argument.env)]).pending) =
      ⟨[(heldSyntax, argument.env)], .finished
        ⟨Space.empty, .returning [], [], [(heldSyntax, argument.env),
          (heldSyntax, argument.env), (heldSyntax, argument.env)]⟩⟩ :=
  represented_service_reply source _

theorem short_budget_retains_the_complete_service_reply (source : HE.GroundedDispatch) :
    (dataMachine source).run 1 (RecursiveEncoding.configurationData (heldJob []).pending) =
      ([], .exhausted (RecursiveEncoding.configurationData (heldJob []).ready)) := by
  rw [run_representation]
  simp only [Machine.run, pending_worker_step, representedOutcome]

theorem resuming_service_reply_publishes_once (source : HE.GroundedDispatch) :
    (dataMachine source).run 2 (RecursiveEncoding.configurationData (heldJob []).ready) =
      ([(heldSyntax, argument.env)], .finished (heldJob []).finished) := by
  rw [run_representation]
  simp only [Machine.run, ready_worker_step, finished_worker_step,
    representedOutcome, List.append_nil]
  rfl

private def rawEffect : Atom := .expression [.symbol "println!", .symbol "held"]
private def rawError : Atom := .expression [.symbol "Error", .symbol "held"]

theorem raw_effect_syntax_is_a_single_uncommitted_reply (space : Space) (source : HE.GroundedDispatch) :
    evalAtom space source rawEffect Atom.atomType Bindings.empty 1 = [(rawEffect, Bindings.empty)] := rfl

theorem raw_error_remains_in_the_argument_packet (space : Space) (source : HE.GroundedDispatch) :
    interpretArgs space source [heldSyntax, rawError, rawEffect]
      [Atom.atomType, Atom.atomType, Atom.atomType] argument.env 4 =
      [(argumentPacket [heldSyntax, rawError, rawEffect], argument.env)] :=
  interpretArgs_raw space source _ _ 4 (by decide)

theorem typed_expression_is_not_admitted_as_a_leaf :
    ¬LeafRel rawEffect (.symbol "Number") := by
  rw [leaf_gate]
  decide

private def unaryArrow : Atom := .expression [.symbol "->", Atom.atomType, .symbol "Result"]
private def binaryArrow : Atom := .expression [.symbol "->", Atom.atomType, Atom.atomType, .symbol "Result"]
private def selectedPolicy : SelectedTypePolicy := ⟨unaryArrow, [Atom.atomType], .symbol "Result", rfl⟩

theorem selected_arrow_leaves_every_suffix_unvisited (space : Space) (suffix : List Atom) :
    FirstSuccessRecursiveStrategy.select space (.expression [.symbol "hold", heldSyntax])
      Atom.undefinedType Bindings.empty 1 (unaryArrow :: suffix) =
      .selected selectedPolicy [Bindings.empty] := by
  exact FirstSuccessRecursiveStrategy.select_success_replicate suffix rfl
    (FirstSuccessSourceApplicability.source_raw_applicability
      space (.symbol "hold") (.symbol "Result") [heldSyntax] Bindings.empty 0)
    (FirstSuccessSourceApplicability.pathCount_positive space [heldSyntax])

theorem wrong_arity_prefix_still_selects_the_first_success (space : Space) (suffix : List Atom) :
    ∃ policy, policy.argumentTypes = [Atom.atomType] ∧
      policy.returnType = .symbol "Result" ∧
      FirstSuccessRecursiveStrategy.select space (.expression [.symbol "hold", heldSyntax])
        Atom.undefinedType Bindings.empty 1 (binaryArrow :: policy.functionType :: suffix) =
        .selected policy [Bindings.empty] ∧
      FunctionCandidateScanRel PublishedCandidateApplicabilityRel space
        (.expression [.symbol "hold", heldSyntax]) Atom.undefinedType Bindings.empty
        (binaryArrow :: policy.functionType :: suffix) (.success policy Bindings.empty) := by
  have rejected : FirstSuccessSourceScan.RejectedPrefix space 0 (.symbol "hold") Atom.undefinedType
      [heldSyntax] [binaryArrow]
      [⟨binaryArrow, .error [mkError (.expression [.symbol "hold", heldSyntax])
        .incorrectNumberOfArguments]⟩] :=
    .wrongArity (domains := [Atom.atomType, Atom.atomType]) (returned := .symbol "Result")
      (by decide) .nil
  exact FirstSuccessSourceScan.raw_prefix_selected rejected (.symbol "Result") Bindings.empty suffix

theorem repeated_type_paths_remain_two_binding_occurrences :
    checkIfFunctionTypeIsApplicable (.expression [.symbol "hold", heldSyntax]) unaryArrow
      Atom.undefinedType (Space.ofList [.expression [.symbol ":", heldSyntax, .symbol "First"],
        .expression [.symbol ":", heldSyntax, .symbol "Second"]]) Bindings.empty 1 =
      .inr [Bindings.empty, Bindings.empty] := rfl

/-- The callback still records both type-check paths, but only its first
binding reaches the evaluation continuation. -/
theorem repeated_type_paths_select_one_binding :
    FirstSuccessRecursiveStrategy.select
      (Space.ofList [.expression [.symbol ":", heldSyntax, .symbol "First"],
        .expression [.symbol ":", heldSyntax, .symbol "Second"]])
      (.expression [.symbol "hold", heldSyntax]) Atom.undefinedType Bindings.empty 1
      [unaryArrow] = .selected selectedPolicy [Bindings.empty] := rfl

theorem repeated_type_paths_do_not_repeat_execution :
    FirstSuccessRecursiveStrategy.select
      (Space.ofList [.expression [.symbol ":", heldSyntax, .symbol "First"],
        .expression [.symbol ":", heldSyntax, .symbol "Second"]])
      (.expression [.symbol "hold", heldSyntax]) Atom.undefinedType Bindings.empty 1
      [unaryArrow] ≠ .selected selectedPolicy [Bindings.empty, Bindings.empty] := by
  rw [repeated_type_paths_select_one_binding]
  intro impossible
  have lists := FirstSuccessRecursiveStrategy.Selection.selected.inj impossible |>.2
  have lengths := congrArg List.length lists
  simp at lengths

private def polymorphicArrow : Atom := .expression [.symbol "->", .var "t", .symbol "Result"]
private def polymorphicPolicy : SelectedTypePolicy :=
  ⟨polymorphicArrow, [.var "t"], .symbol "Result", rfl⟩
private def firstTypeBinding : Bindings := ⟨[("t", .symbol "First")], []⟩
private def secondTypeBinding : Bindings := ⟨[("t", .symbol "Second")], []⟩
private def multiTypedSpace : Space := Space.ofList
  [.expression [.symbol ":", heldSyntax, .symbol "First"],
   .expression [.symbol ":", heldSyntax, .symbol "Second"]]

theorem distinct_callback_frames_remain_ordered :
    checkIfFunctionTypeIsApplicable (.expression [.symbol "hold", heldSyntax]) polymorphicArrow
      Atom.undefinedType multiTypedSpace Bindings.empty 10 =
        .inr [firstTypeBinding, secondTypeBinding] := by decide

theorem first_distinct_binding_is_selected :
    FirstSuccessRecursiveStrategy.select multiTypedSpace
      (.expression [.symbol "hold", heldSyntax]) Atom.undefinedType Bindings.empty 10
      [polymorphicArrow] = .selected polymorphicPolicy [firstTypeBinding] :=
  FirstSuccessRecursiveStrategy.select_success_first [] rfl distinct_callback_frames_remain_ordered

theorem later_distinct_binding_is_not_selected :
    FirstSuccessRecursiveStrategy.select multiTypedSpace
      (.expression [.symbol "hold", heldSyntax]) Atom.undefinedType Bindings.empty 10
      [polymorphicArrow] ≠ .selected polymorphicPolicy [secondTypeBinding] := by
  rw [first_distinct_binding_is_selected]
  intro impossible
  have lists := FirstSuccessRecursiveStrategy.Selection.selected.inj impossible |>.2
  have first := List.cons.inj lists |>.1
  have values := congrArg Bindings.assignments first
  simp [firstTypeBinding, secondTypeBinding] at values

theorem zero_applicability_budget_has_no_rejection_evidence :
    checkIfFunctionTypeIsApplicable (.expression [.symbol "hold", heldSyntax]) unaryArrow
      Atom.undefinedType Space.empty Bindings.empty 0 = .inl [] := rfl

private def aliasSpace : Space := Space.ofList [.expression [.symbol ":", .symbol "token", .var "A"]]

theorem source_cast_records_expected_to_actual_alias_orientation :
    typeCast (.symbol "token") (.var "B") aliasSpace Bindings.empty 10 =
      [(.symbol "token", ⟨[], [("B", "A")]⟩)] := rfl

theorem reversed_cast_operands_have_a_distinct_binding_representation :
    matchTypes (.var "A") (.var "B") Bindings.empty 10 = [⟨[], [("A", "B")]⟩] ∧
      (⟨[], [("A", "B")]⟩ : Bindings) ≠ ⟨[], [("B", "A")]⟩ := ⟨rfl, by decide⟩

private def badCall : Atom := .expression [.symbol "f", .symbol "x"]
private def badArrow : Atom := .expression [.symbol "->", .symbol "Bool", .symbol "Bool"]
private def badSpace : Space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Number"]]

theorem source_bad_first_argument_reports_one :
    checkIfFunctionTypeIsApplicable badCall badArrow Atom.undefinedType badSpace Bindings.empty 10 =
      .inl [mkError badCall (.badArgType 1 (.symbol "Bool") (.symbol "Number"))] := rfl

theorem one_based_argument_error_is_a_distinct_occurrence :
    mkError badCall (.badArgType 0 (.symbol "Bool") (.symbol "Number")) ≠
      mkError badCall (.badArgType 1 (.symbol "Bool") (.symbol "Number")) := by decide

end Controls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafService
