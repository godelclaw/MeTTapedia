import Mettapedia.OSLF.MeTTaIL.GeneralEquationContexts
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobFiniteWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrderedAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout

/-!
# Exact receipt coverage of the rule-job cursor

The outer cursor consumes every actual inner root result in its emitted order.
Projection retains the complete primitive trace and premise history while
checking the licensed replacement and enclosing endpoint. The theorem applies
to the actual finite work forest, including rejected replacement alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open GeneralPremise.Scheduler GeneralRuleJobs

private theorem root_append_drop_cons {A : Type} (answers future : List A) (cursor : Nat) (answer : A)
    (found : answers[cursor]? = some answer) :
    (answers ++ future).drop cursor = answer :: (answers ++ future).drop (cursor + 1) := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have appended : cursor < (answers ++ future).length := by simp only [List.length_append]; omega
  rw [List.drop_eq_getElem_cons appended, List.getElem_append_left within, same]

def rootProjection (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : GeneralPremise.Execution.Result request.environment request.goal) : Option (Answer request) :=
  match result with
  | .root trace captured completed history target valid =>
      finishRoot request licensed trace captured completed history target valid

theorem root_tree_readouts (request : Request) (frame : Frame request)
    (forest : InnerForest request frame.state)
    (tree : TaskTree (expand request) (.root frame)) :
    tree.answers = ((frame.state.answers ++ forest.answers).drop frame.cursor).filterMap
      (rootProjection request frame.licensed) := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralPremise.Scheduler.settled frame.state = true
          · have empty : frame.state.agenda = [] := List.isEmpty_iff.mp idle
            have forestEmpty := forest.answers_empty empty
            have past := List.getElem?_eq_none_iff.mp found
            have tasks : (expand request (.root frame)).tasks = [] := by
              simp only [expand, found, idle, ↓reduceIte]
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            cases selectedChildrenEq : selectedChildren
            simp only [TaskTree.answers]
            have noAnswers : (expand request (.root frame)).answers = [] := by
              simp only [expand, found, idle, ↓reduceIte]
            rw [noAnswers, List.nil_append, ← sameAnswers]
            change selectedChildren.answers = _
            rw [selectedChildrenEq]
            simp only [TaskForest.answers, forestEmpty, List.append_nil, List.drop_eq_nil_of_le past, List.filterMap_nil]
          · have tasks : (expand request (.root frame)).tasks =
                [Task.root {frame with state := GeneralPremise.Execution.tick request.environment request.goal frame.state}] := by
              simp only [expand, found, Bool.eq_false_iff.mpr idle, Bool.false_eq_true, if_false]
            let selectedChildren := tasks ▸ children
            have sameAnswers := TaskForest.answers_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := root_tree_readouts request {frame with
                    state := GeneralPremise.Execution.tick request.environment request.goal frame.state}
                  (forest.advance frame.state) child
                have noAnswers : (expand request (.root frame)).answers = [] := by
                  simp only [expand, found, Bool.eq_false_iff.mpr idle, Bool.false_eq_true, if_false]
                simp only [TaskTree.answers, noAnswers, List.nil_append]
                rw [← sameAnswers]
                change selectedChildren.answers = _
                rw [selectedChildrenEq]
                simp only [TaskForest.answers, List.append_nil]
                rw [later]
                change (((GeneralPremise.Execution.tick request.environment request.goal frame.state).answers ++
                  (forest.advance frame.state).answers).drop frame.cursor).filterMap
                  (rootProjection request frame.licensed) = _
                simp only [GeneralPremise.Execution.tick]
                rw [forest.advance_answers frame.state]
      | some current =>
          have tasks : (expand request (.root frame)).tasks =
              [Task.root {frame with cursor := frame.cursor + 1}] := by
            cases current with
            | root trace captured completed history target valid =>
                simp only [expand, found]
          let selectedChildren := tasks ▸ children
          have sameAnswers := TaskForest.answers_cast tasks children
          have sameCost := TaskForest.cost_cast tasks children
          cases selectedChildrenEq : selectedChildren with
          | cons child tail =>
              cases tail
              have later := root_tree_readouts request {frame with cursor := frame.cursor + 1} forest child
              have emitted : (expand request (.root frame)).answers =
                  (rootProjection request frame.licensed current).toList := by
                cases current with
                | root trace captured completed history target valid =>
                    simp only [expand, found, rootProjection]
              simp only [TaskTree.answers, emitted]
              rw [← sameAnswers]
              change (rootProjection request frame.licensed current).toList ++ selectedChildren.answers = _
              rw [selectedChildrenEq]
              simp only [TaskForest.answers, List.append_nil]
              rw [later, root_append_drop_cons frame.state.answers forest.answers frame.cursor current found]
              cases projected : rootProjection request frame.licensed current <;>
                simp only [List.filterMap_cons, projected, Option.toList_none, Option.toList_some, List.nil_append,
                  List.singleton_append]
termination_by tree.cost
decreasing_by
  all_goals
    change selectedChildren.cost = children.cost at sameCost
    rw [selectedChildrenEq] at sameCost
    simp only [TaskForest.cost] at sameCost
    omega

theorem finishState_root_readouts (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    (finishState request licensed).answers =
      (GeneralPremise.Execution.treeStart request.environment request.goal).answers.filterMap
        (rootProjection request licensed) := by
  rw [(finishState_readouts request licensed).1]
  simp only [startForest, TaskForest.answers, List.append_nil]
  rw [root_tree_readouts request _
    (.cons (GeneralPremise.Execution.treeStart request.environment request.goal) .nil)]
  simp only [GeneralPremise.Execution.start, TaskForest.answers, List.nil_append, List.append_nil,
    List.drop_zero]

theorem finishState_contains_root_result (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : GeneralPremise.Execution.Result request.environment request.goal) (answer : Answer request)
    (member : result ∈ (GeneralPremise.Execution.treeStart request.environment request.goal).answers)
    (projected : rootProjection request licensed result = some answer) :
    answer ∈ (finishState request licensed).answers := by
  rw [finishState_root_readouts]
  exact List.mem_filterMap.mpr ⟨result, member, projected⟩

#print axioms root_tree_readouts
#print axioms finishState_root_readouts


theorem reachable_run_witness {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : State request} (reached : Reachable request licensed state) :
    ∃ fuel, state = run request fuel (start request licensed) := by
  induction reached with
  | start => exact ⟨0, rfl⟩
  | @tick state reached ih =>
      obtain ⟨fuel, same⟩ := ih
      subst state
      exact ⟨fuel + 1, by rw [run_add]; rfl⟩

theorem settled_reachable_finishState {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : State request} (reached : Reachable request licensed state)
    (idle : settled state = true) : state = finishState request licensed := by
  obtain ⟨fuel, same⟩ := reachable_run_witness reached
  subst state
  exact settled_run_unique (expand request) (start request licensed) fuel (workBound request licensed)
    (List.isEmpty_iff.mp idle) (finishState_settled request licensed)

theorem completed_reachable_finishState {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {state : State request} (reached : Reachable request licensed state)
    (finished : complete state = true) : state = finishState request licensed :=
  settled_reachable_finishState reached (List.isEmpty_iff.mpr ((complete_iff state).mp finished).1)

theorem finishState_exact_roots (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (answer : Answer request) :
    answer ∈ (finishState request licensed).answers ↔
      ∃ result ∈ (GeneralPremise.Execution.treeStart request.environment request.goal).answers,
        rootProjection request licensed result = some answer := by
  rw [finishState_root_readouts, List.mem_filterMap]

#print axioms settled_reachable_finishState
#print axioms finishState_exact_roots


theorem projection_job {request : Request}
    {licensed : request.job.Valid request.plan request.bound request.expected request.source}
    {result : GeneralPremise.Execution.Result request.environment request.goal} {answer : Answer request}
    (projected : rootProjection request licensed result = some answer) : answer.val.job = request.job := by
  cases result with
  | root trace captured completed history target valid =>
      simp only [rootProjection] at projected
      unfold finishRoot finishRootIn at projected
      split at projected
      · split at projected
        · cases Option.some.inj projected
          rfl
        · simp at projected
      · simp at projected

theorem finishState_receipt_complete {request : Request}
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    {receipt : Receipt} (valid : receipt.Valid request.plan request.bound request.expected request.source)
    (job : receipt.job = request.job) :
    ∃ answer ∈ (finishState request licensed).answers, answer.val = receipt := by
  let wanted : GeneralPremise.Execution.Result request.environment request.goal :=
    .root receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget
      (job ▸ valid.2.1)
  have ordered : wanted.ordered = true :=
    (job ▸ valid.2.1).ordered checked
  have member := GeneralPremise.Execution.finish_contains request.environment request.goal wanted ordered
  rw [GeneralPremise.Execution.finish_answers] at member
  obtain ⟨answer, finished, same⟩ := finishRoot_complete valid job
  have projected : rootProjection request licensed wanted = some answer := finished
  exact ⟨answer, finishState_contains_root_result request licensed wanted answer member projected, same⟩

theorem finishState_receipt_iff (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : Receipt) :
    receipt ∈ (finishState request licensed).answers.map Subtype.val ↔
      receipt.Valid request.plan request.bound request.expected request.source ∧ receipt.job = request.job := by
  constructor
  · intro member
    obtain ⟨answer, present, same⟩ := List.mem_map.mp member
    subst receipt
    obtain ⟨result, _, projected⟩ := (finishState_exact_roots request licensed answer).mp present
    exact ⟨answer.property, projection_job projected⟩
  · rintro ⟨valid, same⟩
    obtain ⟨answer, member, same⟩ := finishState_receipt_complete licensed checked valid same
    exact List.mem_map.mpr ⟨answer, member, same⟩

/-- Finish every licensed physical job in authored declaration/site order.
Each inner list is the original cursor's ordered readout; identical receipt
values remain separate list occurrences. -/
def completedReceipts (plan : GeneralExecutionAdmission.Plan) (bound : List Syntax.TypeExpr)
    (expected : Syntax.TypeExpr) (source : Syntax.Pattern) : List Receipt :=
  (GeneralRuleJobs.jobs plan bound expected source).attach.flatMap fun item =>
    let request : Request := ⟨plan, bound, expected, source, item.val⟩
    let licensed := (GeneralRuleJobs.jobs_spec plan bound expected source item.val).mp item.property
    (finishState request licensed).answers.map Subtype.val

/-- Every emitted receipt retains its validity witness. Soundness of this
readout does not require the stratification used for complete coverage. -/
theorem completedReceipts_valid {plan : GeneralExecutionAdmission.Plan}
    {bound : List Syntax.TypeExpr} {expected : Syntax.TypeExpr} {source : Syntax.Pattern}
    {receipt : Receipt} (present : receipt ∈ completedReceipts plan bound expected source) :
    receipt.Valid plan bound expected source := by
  obtain ⟨item, _, present⟩ := List.mem_flatMap.mp present
  obtain ⟨answer, _, rfl⟩ := List.mem_map.mp present
  exact answer.property

/-- Exhausting the original per-job cursors covers every original valid
receipt at every permitted typed site. Stratification comes from the actual
preceding-declaration admission check. -/
theorem mem_completedReceipts_iff (plan : GeneralExecutionAdmission.Plan)
    (bound : List Syntax.TypeExpr) (expected : Syntax.TypeExpr) (source : Syntax.Pattern)
    (checked : GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (receipt : Receipt) :
    receipt ∈ completedReceipts plan bound expected source ↔
      receipt.Valid plan bound expected source := by
  constructor
  · exact completedReceipts_valid
  · intro valid
    let item : {job // job ∈ GeneralRuleJobs.jobs plan bound expected source} :=
      ⟨receipt.job, (GeneralRuleJobs.jobs_spec plan bound expected source receipt.job).mpr valid.1⟩
    apply List.mem_flatMap.mpr
    refine ⟨item, List.mem_attach _ _, ?_⟩
    exact (finishState_receipt_iff ⟨plan, bound, expected, source, item.val⟩
      ((GeneralRuleJobs.jobs_spec plan bound expected source item.val).mp item.property)
      checked receipt).mpr ⟨valid, rfl⟩

#print axioms finishState_receipt_complete
#print axioms finishState_receipt_iff

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open Syntax GeneralTypedSites GeneralExecutionAdmission GeneralRuleJobs

/-- Original admission compilation identifies the source row by its actual
declaration index independently of the selected execution ordinal. -/
theorem guarded_receipt_authored_origin
    {snapshot : Snapshot} {permissions : Permissions} {bound : List TypeExpr} {sort : TypeExpr} {source : Pattern}
    (receipt : Receipt) (valid : receipt.Valid (compile snapshot permissions) bound sort source) :
    snapshot.language.rewrites[receipt.job.declaration.declarationIndex]? = some receipt.job.declaration.authored ∧
      selected permissions.ruleIndices receipt.job.declaration.declarationIndex = true ∧
      (GeneralPlanEnvironment.environment (compile snapshot permissions)).language.rewrites[receipt.job.ordinal]? =
        some receipt.job.declaration.rule := by
  have member : receipt.job.declaration ∈ (compile snapshot permissions).rules :=
    List.fst_mem_of_mem_zipIdx valid.1.1
  obtain ⟨rule, index, declared, selected, compiled⟩ := compiled_rule_origin member
  have readout := rulePlan_readout compiled
  refine ⟨?_, ?_, Job.selected_rule valid.1⟩
  · rw [readout.1, readout.2.1]
    exact List.mk_mem_zipIdx_iff_getElem?.mp declared
  · simpa only [readout.1] using selected

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open GeneralPremise
open DerivedContexts
open GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open ConditionalEquationExecution
open GeneralPremise.Execution

theorem licensed_focus_free_within (footprint : List String) (language : LanguageDef)
    (free : FreeTypeContext) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (site : SiteData)
    (licensed : Licensed language free permissions bound type source site)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ site.focus.freeFvarNames, name ∈ footprint := by
  intro name occurs
  apply covered name
  rw [← licensed.source_eq]
  exact (GeneralEquationContexts.fill_contains_source site.context site.focus).2.1 name occurs

theorem licensed_fill_free_within (footprint : List String) (language : LanguageDef)
    (free : FreeTypeContext) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (site : SiteData)
    (licensed : Licensed language free permissions bound type source site)
    (target : Pattern) (before : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (after : ∀ name ∈ target.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ (site.context.fill target).freeFvarNames, name ∈ footprint := by
  intro name occurs
  rcases (GeneralEquationContexts.fill_support_sources site.context site.focus target).2.1 name occurs
    with occurs | occurs
  · exact before name (licensed.source_eq ▸ occurs)
  · exact after name occurs

theorem request_run_finite_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) (fuel : Nat) :
    stateFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)
      request.environment request.goal
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ request.environment.provider
      (fun name member => List.mem_append_right _ member)
      (provider_covered_by_own_names request.environment.provider)
  · exact Query.DynamicOutputsFreeWithin.of_empty _ _ rfl
  · exact licensed_focus_free_within _ _ _ _ _ _ _ _ licensed.2
      (fun _ occurs => List.mem_append_left _ occurs)

theorem request_run_root_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)).answers) :
    assignmentFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) captured ∧
    assignmentFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) completed ∧
    (∀ name ∈ target.freeFvarNames,
      name ∈ request.source.freeFvarNames ++ providerFreeNames request.environment.provider) :=
  ((request_run_finite_free_within request licensed fuel).2 _ member).2

theorem request_run_global_target_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)).answers) :
    ∀ name ∈ (request.job.site.context.fill target).freeFvarNames,
      name ∈ request.source.freeFvarNames ++ providerFreeNames request.environment.provider :=
  licensed_fill_free_within _ _ _ _ _ _ _ _ licensed.2 target
    (fun _ occurs => List.mem_append_left _ occurs)
    (request_run_root_free_within request licensed fuel trace captured completed history target valid member).2.2

theorem request_run_global_checker_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)).answers) :
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected (request.job.site.context.fill target) =
    checkOpenPatternWellSorted request.environment.language request.environment.free
      request.bound request.expected (request.job.site.context.fill target) :=
  check_open_pattern_snapshot _ _ _ _ _ _
    (request_run_global_target_free_within request licensed fuel trace captured completed history target valid member)

theorem finish_root_some_iff_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)).answers) :
    (∃ answer : GeneralRuleJobExecution.Answer request,
      GeneralRuleJobExecution.finishRoot request licensed trace captured completed history target valid = some answer ∧
      answer.val = ⟨request.job, trace, captured, completed, history, target, request.job.site.context.fill target⟩) ↔
    request.job.site.acceptsReplacementRepresentation request.environment.language target = true ∧
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected (request.job.site.context.fill target) = true := by
  rw [request_run_global_checker_snapshot request licensed fuel trace captured completed history target valid member]
  exact GeneralRuleJobExecution.finishRootIn_some_iff GeneralPremise.ordinaryInterpretation
    request licensed trace captured completed history target valid

theorem finish_root_none_iff_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run request.environment request.goal fuel (Execution.start request.environment request.goal)).answers) :
    GeneralRuleJobExecution.finishRoot request licensed trace captured completed history target valid = none ↔
    request.job.site.acceptsReplacementRepresentation request.environment.language target = false ∨
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected (request.job.site.context.fill target) = false := by
  rw [request_run_global_checker_snapshot request licensed fuel trace captured completed history target valid member]
  exact GeneralRuleJobExecution.finishRootIn_none_iff GeneralPremise.ordinaryInterpretation
    request licensed trace captured completed history target valid

def jobTaskFreeWithin (footprint : List String) {request : GeneralRuleJobExecution.Request} :
    GeneralRuleJobExecution.Task request → Prop
  | .root frame => stateFreeWithin footprint request.environment request.goal frame.state

def jobAnswerFreeWithin (footprint : List String) {request : GeneralRuleJobExecution.Request}
    (answer : GeneralRuleJobExecution.Answer request) : Prop :=
  assignmentFreeWithin footprint answer.val.captured ∧
  assignmentFreeWithin footprint answer.val.completed ∧
  (∀ name ∈ answer.val.localTarget.freeFvarNames, name ∈ footprint) ∧
  (∀ name ∈ answer.val.target.freeFvarNames, name ∈ footprint)

def jobStateFreeWithin (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (state : GeneralRuleJobExecution.State request) : Prop :=
  (∀ task ∈ state.agenda, jobTaskFreeWithin footprint task) ∧
  (∀ answer ∈ state.answers, jobAnswerFreeWithin footprint answer)

theorem finish_root_free_within (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (source : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (before : assignmentFreeWithin footprint captured) (after : assignmentFreeWithin footprint completed)
    (localTarget : ∀ name ∈ target.freeFvarNames, name ∈ footprint)
    (answer : GeneralRuleJobExecution.Answer request)
    (emitted : GeneralRuleJobExecution.finishRoot request licensed trace captured completed history target valid = some answer) :
    jobAnswerFreeWithin footprint answer := by
  unfold GeneralRuleJobExecution.finishRoot GeneralRuleJobExecution.finishRootIn at emitted
  split at emitted
  · split at emitted
    · cases Option.some.inj emitted
      exact ⟨before, after, localTarget,
        licensed_fill_free_within footprint _ _ _ _ _ _ _ licensed.2 target source localTarget⟩
    · contradiction
  · contradiction

theorem job_expansion_free_within (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (source : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (provider : ∀ row ∈ request.environment.provider.rows, patternsFreeWithin footprint row.values)
    (task : GeneralRuleJobExecution.Task request) (covered : jobTaskFreeWithin footprint task) :
    (∀ next ∈ (GeneralRuleJobExecution.expand request task).tasks, jobTaskFreeWithin footprint next) ∧
    (∀ answer ∈ (GeneralRuleJobExecution.expand request task).answers, jobAnswerFreeWithin footprint answer) := by
  cases task with
  | root frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          simp only [GeneralRuleJobExecution.expand, found]
          split
          · constructor <;> intro item member <;> cases member
          · constructor
            · intro next member
              rcases List.mem_singleton.mp member with rfl
              exact tick_free_within footprint request.environment request.goal provider
                (Query.DynamicOutputsFreeWithin.of_empty _ _ rfl) frame.state covered
            · intro answer member; cases member
      | some result =>
          have produced := covered.2 result (List.mem_of_getElem? found)
          cases result with
          | root trace captured completed history target valid =>
              simp only [GeneralRuleJobExecution.expand, found]
              constructor
              · intro next member
                rcases List.mem_singleton.mp member with rfl
                exact covered
              · intro answer member
                have emitted : GeneralRuleJobExecution.finishRoot request frame.licensed
                    trace captured completed history target valid = some answer := by
                  cases completed : GeneralRuleJobExecution.finishRoot request frame.licensed
                      trace captured completed history target valid with
                  | none => simp [completed] at member
                  | some returned =>
                      simp only [completed, Option.toList_some, List.mem_singleton] at member
                      subst answer
                      rfl
                exact finish_root_free_within footprint request frame.licensed trace captured completed history target
                  valid source produced.2.1 produced.2.2.1 produced.2.2.2 answer emitted

theorem job_tick_free_within (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (source : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (provider : ∀ row ∈ request.environment.provider.rows, patternsFreeWithin footprint row.values)
    (state : GeneralRuleJobExecution.State request) (covered : jobStateFreeWithin footprint request state) :
    jobStateFreeWithin footprint request (GeneralRuleJobExecution.tick request state) :=
  Scheduler.tick_preserves (jobTaskFreeWithin footprint) (jobAnswerFreeWithin footprint)
    (GeneralRuleJobExecution.expand request) (job_expansion_free_within footprint request source provider) state covered

theorem job_run_free_within (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (source : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (provider : ∀ row ∈ request.environment.provider.rows, patternsFreeWithin footprint row.values)
    (fuel : Nat) (state : GeneralRuleJobExecution.State request) (covered : jobStateFreeWithin footprint request state) :
    jobStateFreeWithin footprint request (GeneralRuleJobExecution.run request fuel state) :=
  Scheduler.run_preserves (jobTaskFreeWithin footprint) (jobAnswerFreeWithin footprint)
    (GeneralRuleJobExecution.expand request) (job_expansion_free_within footprint request source provider) fuel state covered

theorem job_start_free_within (footprint : List String) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (source : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    jobStateFreeWithin footprint request (GeneralRuleJobExecution.start request licensed) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    apply start_free_within
    exact licensed_focus_free_within _ _ _ _ _ _ _ _ licensed.2 source
  · intro answer member; cases member

theorem job_run_finite_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) (fuel : Nat) :
    jobStateFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) request
      (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed)) :=
  job_run_free_within _ request (fun _ member => List.mem_append_left _ member)
    (provider_coverage_mono _ _ request.environment.provider
      (fun _ member => List.mem_append_right _ member) (provider_covered_by_own_names request.environment.provider))
    fuel _ (job_start_free_within _ request licensed (fun _ member => List.mem_append_left _ member))

theorem job_frame_result_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (frame : GeneralRuleJobExecution.Frame request)
    (present : GeneralRuleJobExecution.Task.root frame ∈
      (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed)).agenda)
    (result : Execution.Result request.environment request.goal) (member : result ∈ frame.state.answers) :
    resultFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) result :=
  ((job_run_finite_free_within request licensed fuel).1 _ present).2 result member

theorem job_frame_global_checker_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (frame : GeneralRuleJobExecution.Frame request)
    (present : GeneralRuleJobExecution.Task.root frame ∈
      (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed)).agenda)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈ frame.state.answers) :
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected (request.job.site.context.fill target) =
    checkOpenPatternWellSorted request.environment.language request.environment.free
      request.bound request.expected (request.job.site.context.fill target) := by
  apply check_open_pattern_snapshot
  exact licensed_fill_free_within _ _ _ _ _ _ _ _ licensed.2 target
    (fun _ occurs => List.mem_append_left _ occurs)
    (job_frame_result_free_within request licensed fuel frame present _ member).2.2.2

theorem job_frame_finish_root_some_iff_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (frame : GeneralRuleJobExecution.Frame request)
    (present : GeneralRuleJobExecution.Task.root frame ∈
      (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed)).agenda)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern)
    (valid : RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈ frame.state.answers) :
    (∃ answer : GeneralRuleJobExecution.Answer request,
      GeneralRuleJobExecution.finishRoot request frame.licensed trace captured completed history target valid = some answer ∧
      answer.val = ⟨request.job, trace, captured, completed, history, target, request.job.site.context.fill target⟩) ↔
    request.job.site.acceptsReplacementRepresentation request.environment.language target = true ∧
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected (request.job.site.context.fill target) = true := by
  rw [job_frame_global_checker_snapshot request licensed fuel frame present trace captured completed history target valid member]
  exact GeneralRuleJobExecution.finishRootIn_some_iff GeneralPremise.ordinaryInterpretation
    request frame.licensed trace captured completed history target valid

theorem job_reachable_finite_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (state : GeneralRuleJobExecution.State request) (reached : GeneralRuleJobExecution.Reachable request licensed state) :
    jobStateFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) request state := by
  induction reached with
  | start => exact job_start_free_within _ request licensed (fun _ member => List.mem_append_left _ member)
  | tick reached ih =>
      exact job_tick_free_within _ request (fun _ member => List.mem_append_left _ member)
        (provider_coverage_mono _ _ request.environment.provider
          (fun _ member => List.mem_append_right _ member) (provider_covered_by_own_names request.environment.provider)) _ ih

theorem job_observed_receipt_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (receipt : GeneralRuleJobs.Receipt)
    (observed : receipt ∈ (GeneralRuleJobExecution.run request fuel
      (GeneralRuleJobExecution.start request licensed)).answers.map Subtype.val) :
    assignmentFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) receipt.captured ∧
    assignmentFreeWithin (request.source.freeFvarNames ++ providerFreeNames request.environment.provider) receipt.completed ∧
    (∀ name ∈ receipt.localTarget.freeFvarNames,
      name ∈ request.source.freeFvarNames ++ providerFreeNames request.environment.provider) ∧
    (∀ name ∈ receipt.target.freeFvarNames,
      name ∈ request.source.freeFvarNames ++ providerFreeNames request.environment.provider) := by
  rcases List.mem_map.mp observed with ⟨answer, member, rfl⟩
  exact (job_run_finite_free_within request licensed fuel).2 answer member

theorem job_observed_receipt_checkers_snapshot (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (receipt : GeneralRuleJobs.Receipt)
    (observed : receipt ∈ (GeneralRuleJobExecution.run request fuel
      (GeneralRuleJobExecution.start request licensed)).answers.map Subtype.val) :
    ConditionalEquationExecution.checkAssignment request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      receipt.job.context.bound receipt.job.context.rule receipt.job.context.spec receipt.captured =
      checkTypedAssignment request.environment receipt.job.context receipt.captured ∧
    ConditionalEquationExecution.checkAssignment request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      receipt.job.context.bound receipt.job.context.rule receipt.job.context.spec receipt.completed =
      checkTypedAssignment request.environment receipt.job.context receipt.completed ∧
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      receipt.job.site.focusBound receipt.job.site.focusType receipt.localTarget =
      checkOpenPatternWellSorted request.environment.language request.environment.free
        receipt.job.site.focusBound receipt.job.site.focusType receipt.localTarget ∧
    checkOpenPatternWellSorted request.environment.language
      (FreeTypeContext.ofList (request.environment.free.entriesOn
        (request.source.freeFvarNames ++ providerFreeNames request.environment.provider)))
      request.bound request.expected receipt.target =
      checkOpenPatternWellSorted request.environment.language request.environment.free
        request.bound request.expected receipt.target := by
  have covered := job_observed_receipt_free_within request licensed fuel receipt observed
  refine ⟨?_, ?_, check_open_pattern_snapshot _ _ _ _ _ _ covered.2.2.1,
    check_open_pattern_snapshot _ _ _ _ _ _ covered.2.2.2⟩
  · unfold checkTypedAssignment
    exact ConditionalEquationExecution.checkAssignment_snapshot _ _ _ _ _ _ _
      (assignment_free_names_covered _ _ covered.1)
  · unfold checkTypedAssignment
    exact ConditionalEquationExecution.checkAssignment_snapshot _ _ _ _ _ _ _
      (assignment_free_names_covered _ _ covered.2.1)

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.licensed_focus_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.licensed_fill_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_root_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_global_target_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_global_checker_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.finish_root_some_iff_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.finish_root_none_iff_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.jobTaskFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.jobAnswerFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.jobStateFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.finish_root_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_tick_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_run_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_start_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_frame_result_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_frame_global_checker_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_frame_finish_root_some_iff_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_reachable_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_observed_receipt_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.job_observed_receipt_checkers_snapshot

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
