import GoalReview

/-!
# Executable checks for the periodic review obligation

These finite model traces exercise the boundary with the existing broker and
request ledger. The example checker recognizes a fixed test payload; it does
not validate natural-language review content or a deployed implementation.
-/

namespace GoalReviewChecks

open GoalReview
open Mettapedia.CognitiveArchitecture.Agent

def cfg : Config where
  interval := 3
  positive := by decide
  key := fun round => ⟨1, round, 100⟩
  key_injective := by
    intro a b h
    exact congrArg ConversationContinuation.RequestKey.epoch h

def checks (_ : ConversationContinuation.RequestKey) (r : ConversationContinuation.Receipt) : Bool :=
  r.payload == 42

def task : ConversationContinuation.RequestKey := ⟨1, 0, 7⟩
def steering : ConversationContinuation.RequestKey := ⟨1, 0, 8⟩
def ticket : ConversationContinuation.Ticket := ⟨cfg.key 0, 1⟩
def receipt : ConversationContinuation.Receipt := ⟨ticket, ⟨.returned, .success⟩, 42⟩

def configured : ObservedStrategy.State :=
  { ObservedStrategy.initial 10 with router := ⟨[10], [10], [10]⟩ }
def active : ObservedStrategy.State :=
  ObservedStrategy.acknowledge (ObservedStrategy.deliver configured task) task
def reviewActive : ObservedStrategy.State :=
  ObservedStrategy.acknowledge (ObservedStrategy.deliver active (cfg.key 0)) (cfg.key 0)
def sampled : ObservedStrategy.State :=
  ObservedStrategy.capture reviewActive 0 (cfg.key 0) []
def proposed : ObservedStrategy.State :=
  ObservedStrategy.reply sampled 0 0 (.command ticket 10)
def returned : ObservedStrategy.State := ObservedStrategy.report proposed receipt
def observed : ObservedStrategy.State := ObservedStrategy.observe returned ticket
def owed : State := ⟨observed, ⟨3, 0⟩⟩
def report : Report := ⟨observed.revision, receipt⟩

theorem interval_reaches_review_with_bounded_salience :
    let state : State := ⟨active, {}⟩
    let later := step cfg checks state (.elapsed 1000)
    later.clock.age = 3 ∧ next cfg later true = .review := by decide

theorem budget_denial_keeps_review_due :
    next cfg owed false = .wait ∧ due cfg owed.clock = true := by decide

theorem incoming_input_preempts_without_paying_debt :
    let state := step cfg checks owed (.operational (.delivered steering))
    next cfg state true = .input ∧ state.clock = owed.clock := by decide

theorem unobserved_return_waits_before_review :
    let state : State := ⟨returned, owed.clock⟩
    next cfg state true = .wait ∧ due cfg state.clock = true := by decide

theorem review_survives_control_recovery_and_time :
    let later := run cfg checks owed
      [.operational .paused, .operational (.modeSelected .iter),
       .operational (.compacted 0), .operational .restarted,
       .operational .resumed, .elapsed 100]
    later.clock = owed.clock ∧ next cfg later true = .review ∧
      later.agent.requests.commitments task = .active := by decide

theorem observed_checked_review_starts_a_fresh_interval :
    let later := acknowledge cfg checks owed report
    later.clock = ⟨0, 1⟩ ∧ next cfg later true = .work ∧
      later.agent.requests.commitments task = .active := by decide

theorem early_checked_review_also_counts :
    let early : State := { owed with clock := ⟨1, 0⟩ }
    due cfg early.clock = false ∧ (acknowledge cfg checks early report).clock = ⟨0, 1⟩ := by decide

theorem missing_observation_cannot_pay :
    let state : State := { owed with agent :=
      { observed with requests := { observed.requests with observed := [] } } }
    canAcknowledge cfg checks state report = false ∧
      (acknowledge cfg checks state report).clock = state.clock := by decide

theorem returned_failure_cannot_pay :
    let failed : ConversationContinuation.Receipt :=
      { receipt with outcome := ⟨.returned, .failure⟩ }
    let state : State := { owed with agent :=
      { observed with requests := { observed.requests with journal := [failed] } } }
    canAcknowledge cfg checks state ⟨observed.revision, failed⟩ = false := by decide

theorem checker_rejection_cannot_pay :
    canAcknowledge cfg (fun _ _ => false) owed report = false ∧
      (acknowledge cfg (fun _ _ => false) owed report).clock = owed.clock := by decide

theorem new_revision_invalidates_an_old_acknowledgement :
    let state := step cfg checks owed (.operational (.modeSelected .omega))
    canAcknowledge cfg checks state report = false ∧
      (acknowledge cfg checks state report).clock = owed.clock := by decide

theorem replayed_receipt_cannot_clear_the_next_review :
    let paid := acknowledge cfg checks owed report
    let later := step cfg checks paid (.elapsed 3)
    due cfg later.clock = true ∧ canAcknowledge cfg checks later report = false ∧
      (acknowledge cfg checks later report).clock = ⟨3, 1⟩ := by decide

end GoalReviewChecks
