import FairGoalStrategy
import GoalReviewChecks

/-!

Historical/design model: this file records a policy studied before the sequential
tool simplification. Its holds, quotas, or scheduling assumptions are not the
current dispatch contract. See `SequentialTools.lean` for that contract and
`CommandHolds.lean` for the conditional costs of the removed hold policy.
# Fair scheduling and request-ledger replays

Shares, costs, periods and payloads here are fixture values, not deployment
defaults. The task checker comes from the existing checked-cycle fixtures.
-/

namespace FairGoalChecks

open GoalSystem
open Mettapedia.CognitiveArchitecture.Agent

def research : Goal := { id := 8, share := 2, baseUrgency := 1000 }
def review : Goal := { GoalReview.goal 100 3 with age := 3 }
def goals : List Goal := [research, review]
def cfg := GoalReviewChecks.cfg
def checks := GoalReviewChecks.checks

def initial : State :=
  let first := cfg.key (research.id, research.round)
  let second := cfg.key (review.id, review.round)
  let a := ObservedStrategy.acknowledge
    (ObservedStrategy.deliver GoalReviewChecks.active first) first
  let b := ObservedStrategy.acknowledge (ObservedStrategy.deliver a second) second
  ⟨b, goals⟩

def submitted : State := FairGoalStrategy.capture cfg true initial 0
  (cfg.key (research.id, research.round)) []

def failed : State := FairGoalStrategy.step cfg checks true submitted
  (.operational (.replied 0 initial.agent.nextSample (.failure 9 1)))

def returned : State := FairGoalStrategy.run cfg checks true submitted
  [.operational (.replied 0 initial.agent.nextSample
     (.command (GoalReviewChecks.ticket research) 10)),
   .operational (.reported (GoalReviewChecks.receipt research))]

def observed : State := FairGoalStrategy.step cfg checks true returned
  (.operational (.observed (GoalReviewChecks.ticket research)))

theorem failing_work_cannot_monopolize_review :
    FairGoalScheduling.trace 6 goals = [8, 100, 8, 8, 100, 8] := by decide

theorem two_to_one_share_is_executable :
    (FairGoalScheduling.run (List.replicate 60 1) goals).map Goal.service = [40, 20] := by decide

theorem small_positive_share_is_not_rounded_away :
    FairGoalScheduling.trace 2 [{ research with share := 1000000 }, review] = [8, 100] := by decide

theorem comparison_uses_exact_fractions :
    let a := { research with service := 3, share := 4 }
    let b := { review with service := 1, share := 2 }
    FairGoalScheduling.select [a, b] = some b := by decide

theorem urgency_breaks_equal_service_ties :
    FairGoalScheduling.select [review, research] = some research := by decide

theorem unbounded_urgency_cannot_override_service (extra : Nat) :
    FairGoalScheduling.select [{ research with service := 1, baseUrgency := extra }, review] =
      some review := by
  simp [FairGoalScheduling.select, FairGoalScheduling.runnable, FairGoalScheduling.prefer,
    eligible, research, review, GoalReview.goal]

theorem zero_share_is_explicitly_ineligible :
    FairGoalScheduling.select [{ research with share := 0 }, review] = some review := by decide

theorem repeated_goal_ids_are_not_a_valid_cohort :
    FairGoalScheduling.UniqueIds goals ∧
    ¬ FairGoalScheduling.UniqueIds [research, research] := by decide

theorem blocked_and_finished_goals_are_excluded :
    FairGoalScheduling.select [{ research with blocked := true },
      { research with id := 9, finished := true }, review] = some review := by decide

theorem review_becomes_due_in_the_same_queue :
    FairGoalScheduling.timedTrace [1, 1, 1, 1]
      [research, { review with age := 0 }] = [8, 8, 100, 8] := by decide

theorem larger_quanta_are_charged_as_service :
    (FairGoalScheduling.run [4, 1, 1] goals).map Goal.service = [4, 2] := by decide

theorem capture_charges_before_the_outcome :
    submitted.goals.map Goal.service = [1, 0] ∧
    submitted.agent.allowance + 1 = initial.agent.allowance ∧
    submitted.agent.requests.commitments (cfg.key (research.id, research.round)) = .active := by decide

theorem provider_failure_does_not_refund_service_or_complete_work :
    failed.goals.map Goal.service = [1, 0] ∧
    failed.agent.requests.commitments (cfg.key (research.id, research.round)) = .active ∧
    failed.goals.map Goal.finished = [false, false] := by decide

theorem old_urgency_policy_disagrees_after_failure :
    GoalSystem.select failed.goals = some { research with service := 1 } ∧
    FairGoalScheduling.select failed.goals = some review := by decide

theorem review_gets_the_next_turn_after_failure :
    let next := FairGoalStrategy.capture cfg true failed 1 (cfg.key (review.id, review.round)) []
    next.goals.map Goal.service = [1, 1] ∧ next.agent.nextSample = 2 := by decide

theorem cooldown_blocks_early_turn_without_charging :
    let next := FairGoalStrategy.capture cfg true failed 0 (cfg.key (review.id, review.round)) []
    next.goals.map Goal.service = [1, 0] ∧ next.agent.nextSample = 1 := by decide

theorem duplicate_capture_is_not_double_charged :
    let again := FairGoalStrategy.capture cfg true submitted 0 (cfg.key (research.id, research.round)) []
    again.goals.map Goal.service = [1, 0] ∧ again.agent.nextSample = 1 := by decide

theorem unselected_focus_cannot_bypass_fairness :
    let wrong := FairGoalStrategy.capture cfg true failed 1 (cfg.key (research.id, research.round)) []
    wrong.goals.map Goal.service = [1, 0] ∧ wrong.agent.nextSample = 1 := by decide

theorem exhausted_provider_budget_does_not_charge :
    let empty := { initial with agent := { initial.agent with allowance := 0 } }
    let next := FairGoalStrategy.capture cfg true empty 0 (cfg.key (research.id, research.round)) []
    next.goals.map Goal.service = [0, 0] ∧ next.agent.pending = none := by decide

theorem unread_input_preempts_without_erasing_service :
    let unread := FairGoalStrategy.step cfg checks true failed
      (.operational (.delivered GoalReviewChecks.steering))
    let next := FairGoalStrategy.capture cfg true unread 1 (cfg.key (review.id, review.round)) []
    FairGoalStrategy.next unread true = .input ∧
    next.goals.map Goal.service = [1, 0] ∧ next.agent.nextSample = 1 := by decide

theorem provider_text_is_neither_a_refund_nor_completion :
    let text := FairGoalStrategy.step cfg checks true submitted
      (.operational (.replied 0 initial.agent.nextSample (.text 42)))
    text.goals.map Goal.service = [1, 0] ∧
    text.agent.requests.commitments (cfg.key (research.id, research.round)) = .active := by decide

theorem unobserved_result_allows_thinking_but_not_completion :
    let attempted := FairGoalStrategy.capture cfg true returned 1 (cfg.key (review.id, review.round)) []
    attempted.goals.map Goal.service = [1, 1] ∧ attempted.agent.nextSample = 2 ∧
    FairGoalStrategy.next returned true = .goal review ∧
    attempted.agent.requests.phase = returned.agent.requests.phase ∧
    canAcknowledge cfg checks returned.agent research
      ⟨research.id, returned.agent.revision, GoalReviewChecks.receipt research⟩ = false := by decide

theorem checked_completion_preserves_service_and_other_obligations :
    let done := FairGoalStrategy.step cfg checks true observed
      (.serviced ⟨research.id, observed.agent.revision, GoalReviewChecks.receipt research⟩)
    done.goals.map Goal.service = [1, 0] ∧
    done.goals.map Goal.finished = [true, false] ∧
    done.agent.requests.commitments GoalReviewChecks.task = .active ∧
    done.agent.requests.commitments (cfg.key (review.id, review.round)) = .active := by decide

theorem recurring_cycle_keeps_its_service_history :
    let spent := { review with service := 7 }
    (afterService spent).service = 7 ∧ (afterService spent).age = 0 ∧
    (afterService spent).round = 1 ∧ (afterService spent).finished = false := by decide

theorem mode_restart_compaction_keep_accounting :
    let recovered := FairGoalStrategy.run cfg checks true submitted
      [.operational .paused, .operational (.modeSelected .omega),
       .operational (.compacted 0), .operational .restarted, .operational .resumed, .elapsed 100]
    recovered.goals.map Goal.service = [1, 0] ∧ recovered.agent.allowance = 9 ∧
    recovered.agent.requests.commitments GoalReviewChecks.task = .active ∧
    FairGoalStrategy.next recovered true = .goal (advance 100 review) := by decide

theorem old_provider_reply_after_restart_cannot_refund :
    let restored := FairGoalStrategy.step cfg checks true submitted (.operational .restarted)
    let late := FairGoalStrategy.step cfg checks true restored
      (.operational (.replied 0 initial.agent.nextSample (.text 42)))
    late.goals.map Goal.service = [1, 0] ∧ late.agent.nextSample = 1 ∧
    late.agent.requests.commitments (cfg.key (research.id, research.round)) = .active := by decide

end FairGoalChecks
