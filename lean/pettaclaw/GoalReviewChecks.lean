import GoalReview

/-!
# Goal review and ordinary work in one queue

Finite model traces use the existing broker and protected request ledger.
The example checker recognizes a fixed test payload; the host must supply a
sound outcome checker for real work. Intervals and priorities are test values.
-/

namespace GoalReviewChecks

open GoalSystem
open Mettapedia.CogArch.Agent

def cfg : Config where
  key := fun pair => ⟨1, pair.2, pair.1⟩
  key_injective := by
    intro a b equal
    apply Prod.ext
    · exact congrArg ConversationContinuation.RequestKey.serial equal
    · exact congrArg ConversationContinuation.RequestKey.epoch equal

def checks (_ : ConversationContinuation.RequestKey) (r : ConversationContinuation.Receipt) : Bool :=
  r.payload == 42

def task : ConversationContinuation.RequestKey := ⟨1, 0, 7⟩
def steering : ConversationContinuation.RequestKey := ⟨1, 0, 9⟩
def research : Goal := { id := 8, baseUrgency := 2 }
def review : Goal := { GoalReview.goal 100 3 with age := 3 }
def ticket (goal : Goal) : ConversationContinuation.Ticket := ⟨cfg.key (goal.id, goal.round), 1⟩
def receipt (goal : Goal) : ConversationContinuation.Receipt :=
  ⟨ticket goal, ⟨.returned, .success⟩, 42⟩

def configured : ObservedStrategy.State :=
  { ObservedStrategy.initial 10 with router := ⟨[10], [10], [10]⟩ }
def active : ObservedStrategy.State :=
  ObservedStrategy.acknowledge (ObservedStrategy.deliver configured task) task

def returnedFrom (agent : ObservedStrategy.State) (goal : Goal) : ObservedStrategy.State :=
  let key := cfg.key (goal.id, goal.round)
  let enlisted := ObservedStrategy.acknowledge (ObservedStrategy.deliver agent key) key
  let sampled := ObservedStrategy.capture enlisted 0 key []
  let proposed := ObservedStrategy.reply sampled 0 enlisted.nextSample (.command (ticket goal) 10)
  ObservedStrategy.report proposed (receipt goal)

def returned (goal : Goal) : ObservedStrategy.State := returnedFrom active goal

def observedFrom (agent : ObservedStrategy.State) (goal : Goal) : ObservedStrategy.State :=
  ObservedStrategy.observe (returnedFrom agent goal) (ticket goal)

def observed (goal : Goal) : ObservedStrategy.State :=
  observedFrom active goal

def owed : State := ⟨observed review, [research, review]⟩
def report (goal : Goal) : Report := ⟨goal.id, (observed goal).revision, receipt goal⟩

theorem ordinary_work_and_review_share_the_selector :
    let early : State := ⟨active, [research, GoalReview.goal 100 3]⟩
    next early true = .goal research ∧ next owed true = .goal review := by decide

theorem due_review_competes_with_other_urgent_work :
    let urgent : Goal := { research with baseUrgency := 100 }
    next { owed with goals := [review, urgent] } true = .goal urgent := by decide

theorem recorded_progress_makes_older_work_salient :
    let advanced := advance 3 research
    let fresh := afterService advanced
    let recurrentWork : Goal := { fresh with recurrence := .every 0, finished := false }
    select [recurrentWork, review] = some review := by decide

theorem blocked_and_finished_goals_are_not_selected :
    let blocked : Goal := { research with baseUrgency := 1000, blocked := true }
    let finished : Goal := { research with id := 20, baseUrgency := 2000, finished := true }
    select [blocked, finished, review] = some review := by decide

theorem equal_urgency_keeps_recorded_order :
    let same : Goal := { review with id := 200 }
    select [review, same] = some review ∧ select [same, review] = some same := by decide

theorem budget_denial_keeps_every_goal :
    next owed false = .wait ∧ (step cfg checks owed (.elapsed 2)).goals =
      [advance 2 research, advance 2 review] := by decide

theorem incoming_input_preempts_without_resetting_age :
    let state := step cfg checks owed (.operational (.delivered steering))
    next state true = .input ∧ state.goals = owed.goals := by decide

theorem unobserved_return_allows_selection_but_not_completion :
    let state : State := { owed with agent := returned review }
    next state true = .goal review ∧ state.goals = owed.goals ∧
      canAcknowledge cfg checks state.agent review
        ⟨review.id, state.agent.revision, receipt review⟩ = false := by decide

theorem goals_survive_control_recovery_and_time :
    let later := run cfg checks owed
      [.operational .paused, .operational (.modeSelected .iter),
       .operational (.compacted 0), .operational .restarted,
       .operational .resumed, .elapsed 100]
    later.goals = [advance 100 research, advance 100 review] ∧
      next later true = .goal (advance 100 review) ∧
      later.agent.requests.commitments task = .active := by decide

theorem checked_review_rearms_in_the_shared_queue :
    let later := acknowledge cfg checks owed (report review)
    later.goals = [research, afterService review] ∧ next later true = .goal research ∧
      later.agent.requests.commitments task = .active ∧
      later.agent.requests.commitments (cfg.key (review.id, review.round)) =
        .discharged ⟨.achieved, .result (receipt review)⟩ := by decide

theorem checked_one_shot_work_finishes_by_the_same_transition :
    let state : State := ⟨observed research, [research, review]⟩
    let later := acknowledge cfg checks state (report research)
    later.goals = [afterService research, review] ∧ next later true = .goal review ∧
      later.agent.requests.commitments (cfg.key (research.id, research.round)) =
        .discharged ⟨.achieved, .result (receipt research)⟩ := by decide

theorem early_checked_review_also_counts :
    let early : State := { owed with goals := [research, { review with age := 1 }] }
    (acknowledge cfg checks early (report review)).goals = [research, afterService review] := by decide

theorem missing_observation_cannot_reset_age :
    let state : State := { owed with agent :=
      { observed review with requests := { (observed review).requests with observed := [] } } }
    canAcknowledge cfg checks state.agent review (report review) = false ∧
      (acknowledge cfg checks state (report review)).goals = state.goals := by decide

theorem returned_failure_cannot_reset_age :
    let failed : ConversationContinuation.Receipt :=
      { receipt review with outcome := ⟨.returned, .failure⟩ }
    let agent : ObservedStrategy.State :=
      { observed review with requests := { (observed review).requests with journal := [failed] } }
    canAcknowledge cfg checks agent review ⟨review.id, agent.revision, failed⟩ = false := by decide

theorem checker_rejection_cannot_pay :
    canAcknowledge cfg (fun _ _ => false) owed.agent review (report review) = false ∧
      (acknowledge cfg (fun _ _ => false) owed (report review)).goals = owed.goals := by decide

theorem new_revision_invalidates_old_acknowledgement :
    let state := step cfg checks owed (.operational (.modeSelected .omega))
    canAcknowledge cfg checks state.agent review (report review) = false ∧
      (acknowledge cfg checks state (report review)).goals = owed.goals := by decide

theorem receipt_cannot_pay_a_different_goal :
    canAcknowledge cfg checks owed.agent research
      { report review with goal := research.id } = false := by decide

theorem receipt_cannot_pay_the_next_cycle :
    let paid := acknowledge cfg checks owed (report review)
    let later := step cfg checks paid (.elapsed 3)
    later.goals = [advance 3 research, advance 3 (afterService review)] ∧
      (acknowledge cfg checks later (report review)).goals = later.goals := by decide

theorem empty_eligible_queue_has_no_selected_goal :
    let waiting : Goal := GoalReview.goal 100 3
    next { owed with goals := [waiting] } true = .idle := by decide

theorem high_urgency_cannot_invent_completion_authority :
    let urgent : Goal := { review with baseUrgency := 1000000 }
    let state : State := ⟨configured, [urgent]⟩
    next state true = .goal urgent ∧
      canAcknowledge cfg checks state.agent urgent
        ⟨urgent.id, configured.revision, receipt urgent⟩ = false := by decide

theorem review_and_research_complete_then_review_runs_again :
    let paidReview := acknowledge cfg checks owed (report review)
    let withResearchResult : State :=
      { paidReview with agent := observedFrom paidReview.agent research }
    let paidResearch := acknowledge cfg checks withResearchResult
      ⟨research.id, withResearchResult.agent.revision, receipt research⟩
    let later := step cfg checks paidResearch (.elapsed 3)
    let again := advance 3 (afterService review)
    let withReviewResult : State := { later with agent := observedFrom later.agent again }
    let paidAgain := acknowledge cfg checks withReviewResult
      ⟨again.id, withReviewResult.agent.revision, receipt again⟩
    next later true = .goal again ∧
      paidAgain.goals = [afterService research, afterService again] ∧
      paidAgain.agent.requests.commitments task = .active ∧
      paidAgain.agent.requests.journal.length = 3 := by decide

end GoalReviewChecks
