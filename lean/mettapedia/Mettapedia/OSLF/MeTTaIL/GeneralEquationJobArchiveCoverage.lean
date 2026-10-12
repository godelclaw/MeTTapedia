import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobSemanticCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralEquationPremiseOrder

/-!
# Semantic coverage of completed archived equation jobs

Every independently justified equation occurrence is present in the actual
drained job, including its ordered premise history and matching trace. A
reachable settled snapshot agrees with that explicit completion strategy;
the theorem does not grant completeness to an arbitrary empty state.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem initial_forest_covers (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (forest : TaskForest (expand request) (start request licensed).agenda)
    (receipt : Receipt) (valid : Completion request.plan request.bound request.expected request.source receipt)
    (sameJob : receipt.job = request.job)
    (ordered : GeneralPremise.eventsOrdered (receipt.job.context request.plan).ruleIndex receipt.premiseHistory = true) :
    receipt ∈ forest.answers.map Subtype.val := by
  have checked := checkOpenPatternWellSorted_complete valid.sourceTyped
  have sourceChecked : checkOpenPatternWellSorted request.environment.language request.plan.snapshot.free
      request.bound request.expected request.source = true := checked
  let frame : MatchFrame request :=
    ⟨licensed, checkOpenPatternWellSorted_sound checked,
      GeneralScopedMatchMachine.start request.matcher, .start, 0⟩
  have tasks : (start request licensed).agenda = [Task.matching frame] := by
    unfold start
    rw [dif_pos sourceChecked]
  let chosen := tasks ▸ forest
  have sameAnswers := TaskForest.answers_cast tasks forest
  cases chosenEq : chosen with
  | cons tree tail =>
      cases tail
      let answer : GeneralScopedMatchMachine.Answer := ⟨receipt.captured, receipt.matcherTrace⟩
      have matching : answer.Valid request.matcher := by
        simpa only [answer, GeneralScopedMatchMachine.Answer.Valid, Request.matcher, sameJob] using valid.matched
      have member : answer ∈ (finishMatcher request.matcher frame.state).answers.drop frame.cursor := by
        change answer ∈ (finishMatcher request.matcher (GeneralScopedMatchMachine.start request.matcher)).answers.drop 0
        rw [List.drop_zero]
        exact (finishMatcher_answers_iff GeneralScopedMatchMachine.Reachable.start answer).mpr matching
      have capturedTyped : GeneralPremise.TypedAssignment request.environment
          (request.job.context request.plan) answer.assignment := sameJob ▸ valid.capturedTyped
      let result : GeneralPremise.Execution.Result request.environment (request.premises answer.assignment) :=
        .premises receipt.completed receipt.premiseHistory (sameJob ▸ valid.premises)
      have resultOrdered : result.ordered = true := by
        simpa only [result, GeneralPremise.Execution.Result.ordered, Request.premises, sameJob] using ordered
      have finished : premiseProjection request answer.trace answer.assignment result = some receipt := by
        simpa only [premiseProjection, result, answer, sameJob] using finish_complete valid
      have emitted := matching_tree_receipts request frame tree answer member capturedTyped
        result resultOrdered receipt finished
      rw [← sameAnswers]
      change receipt ∈ chosen.answers.map Subtype.val
      rw [chosenEq]
      simpa only [TaskForest.answers, List.append_nil] using emitted

theorem finishJob_covers (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (receipt : Receipt) (valid : Completion request.plan request.bound request.expected request.source receipt)
    (sameJob : receipt.job = request.job)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true) :
    receipt ∈ (finishJob request licensed).answers.map Subtype.val := by
  have emitted := initial_forest_covers request licensed
    (startForest request licensed (authoredPremiseForests request)) receipt valid sameJob (valid.ordered checked)
  rw [(finishJob_readouts request licensed).1, List.map_append]
  exact List.mem_append_right _ emitted

theorem settled_answers_complete {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state)
    (idle : settled state = true)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : Receipt) (valid : Completion request.plan request.bound request.expected request.source receipt)
    (sameJob : receipt.job = request.job) : receipt ∈ state.answers.map Subtype.val := by
  rw [settled_reachable_finishJob reached idle]
  exact finishJob_covers request licensed receipt valid sameJob checked

theorem completed_answers_complete {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state)
    (completed : complete state = true)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : Receipt) (valid : Completion request.plan request.bound request.expected request.source receipt)
    (sameJob : receipt.job = request.job) : receipt ∈ state.answers.map Subtype.val :=
  settled_answers_complete reached (List.isEmpty_iff.mpr ((complete_iff state).mp completed).1)
    checked receipt valid sameJob

theorem complete_answers_iff {request : Request}
    {licensed : LicensedJob request.plan request.bound request.expected request.source request.job}
    {state : State request} (reached : Reachable request licensed state)
    (completed : complete state = true)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : Receipt) :
    receipt ∈ state.answers.map Subtype.val ↔
      Completion request.plan request.bound request.expected request.source receipt ∧ receipt.job = request.job := by
  constructor
  · intro member
    obtain ⟨answer, emitted, same⟩ := List.mem_map.mp member
    subst receipt
    exact ⟨answer.property, reachable_requested_answers reached answer emitted⟩
  · rintro ⟨valid, sameJob⟩
    exact completed_answers_complete reached completed checked receipt valid sameJob

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
