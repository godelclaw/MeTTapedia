import ObservedStrategy

/-!
# Finite replays and failure controls for the observed strategy

These are executable model checks at the provider/ledger boundary. They do
not replay Python, C, remote services or a live model. The six counterexamples
exercise explicit broken alternatives to the same transition gates.
-/

namespace ObservedStrategyChecks

open ObservedStrategy
open Mettapedia.CogArch.Agent

def task : ConversationContinuation.RequestKey := ⟨1, 1, 7⟩
def steering : ConversationContinuation.RequestKey := ⟨1, 1, 8⟩
def otherAgent : ConversationContinuation.RequestKey := ⟨2, 1, 7⟩
def ticket : ConversationContinuation.Ticket := ⟨task, 1⟩
def success : ConversationContinuation.Receipt := ⟨ticket, ⟨.returned, .success⟩, 42⟩
def failure : ConversationContinuation.Receipt := ⟨ticket, ⟨.returned, .failure⟩, 13⟩

def configured : State :=
  { initial 10 with
    boundary := ⟨[1, 2], [10]⟩
    router := ⟨[10], [10], [10]⟩ }

def active : State := acknowledge (deliver configured task) task
def sampled : State := capture active 0 task []
def captured : Snapshot := snapshot active task []
def proposed : State := reply sampled 0 0 (.command ticket 10)
def returned : State := report proposed success
def observed : State := observe returned ticket
def newInput : State := acknowledge (deliver sampled steering) steering

theorem transactional_preparation_preserves_authority_and_obligation :
    let snap := snapshot active task
      [IterArchitecture.clearMessages, fun _ => none,
       fun boundary => some { boundary with advertised := [99] }]
    snap.boundary.messages = [] ∧ snap.boundary.advertised = [99] ∧
    snap.obligation = .active ∧ admitCommand snap ticket 99 = none := by decide

theorem pending_work_and_effect_survive_control_changes :
    let next := restore (compact (selectMode (pause proposed) .omega) 0)
    next.requests.commitments task = .active ∧ next.dispatch.isSome = true ∧
    next.requests.issued = [ticket] ∧ next.allowance = 9 ∧ next.nextSample = 1 := by decide

theorem acknowledged_steering_still_invalidates_old_decision :
    let next := reply newInput 0 0 (.command ticket 10)
    next.dispatch = none ∧ next.requests.commitments task = .active ∧
    next.requests.commitments steering = .active ∧ next.decisions = [.stale 0] := by decide

theorem mode_switch_does_not_relabel_old_provider_result :
    let next := reply (selectMode sampled .omega) 0 0 (.command ticket 10)
    next.dispatch = none ∧ next.requests.commitments task = .active ∧
    next.decisions = [.stale 0] := by decide

theorem foreign_request_and_wrong_serial_cannot_dispatch :
    let foreign := reply sampled 0 0 (.command ⟨otherAgent, 1⟩ 10)
    let wrong := reply sampled 0 9 (.command ticket 10)
    foreign.dispatch = none ∧ wrong.pending = sampled.pending ∧
    wrong.decisions = [] := by decide

theorem duplicate_provider_completion_cannot_enqueue_twice :
    let duplicate := reply proposed 0 0 (.command ticket 10)
    duplicate.requests.issued = [ticket] ∧ duplicate.decisions.length = 1 ∧
    duplicate.dispatch = proposed.dispatch := by decide

theorem thinking_continues_before_broker_result_observation :
    (capture proposed 0 task []).nextSample = 2 ∧
    (capture returned 0 task []).nextSample = 2 ∧
    (capture observed 0 task []).nextSample = 2 := by decide

theorem text_reply_preserves_missing_broker_outcome :
    let thinking := capture proposed 0 task []
    let answered := reply thinking 0 1 (.text 77)
    answered.pending = none ∧ answered.dispatch = proposed.dispatch ∧
    answered.requests.phase = .awaitingBroker ticket ∧
    answered.requests.issued = [ticket] ∧ answered.decisions.getLast? = some (.text 1 77) := by decide

theorem late_receipt_invalidates_an_in_flight_plan :
    let thinking := capture proposed 0 task []
    let arrived := report thinking success
    let answered := reply arrived 0 1 (.command ⟨task, 2⟩ 10)
    answered.pending = none ∧ answered.requests.journal = [success] ∧
    answered.requests.issued = [ticket] ∧
    answered.decisions.getLast? = some (.stale 1) := by decide

theorem task_fulfillment_needs_the_task_checker :
    returned.requests.commitments task = .active ∧
    (finish (fun _ _ => false) observed task success).requests.commitments task = .active ∧
    (finish (fun _ _ => true) observed task success).requests.commitments task =
      .discharged ⟨.achieved, .result success⟩ := by decide

theorem failed_provider_attempt_spends_once_and_can_recover :
    let failed := reply sampled 0 0 (.failure 13 0)
    failed.requests.commitments task = .active ∧ failed.allowance = 9 ∧
    failed.nextSample = 1 ∧ failed.cooldownUntil = 1 ∧
    (capture failed 0 task []).nextSample = 1 ∧
    (capture failed 1 task []).nextSample = 2 := by decide

theorem exhausted_budget_and_rest_retain_work :
    let exhausted := { active with allowance := 0 }
    let rested := cooldown exhausted 1800
    (capture rested 1800 task []).nextSample = 0 ∧
    rested.requests.commitments task = .active ∧
    ConversationContinuation.idleAllowed rested.requests = false := by decide

theorem provider_submission_arms_wake_without_completing_work :
    sampled.omega.nextWake = some 600 ∧
    (omegaWake sampled 600).omega.loops = sampled.omega.loops ∧
    (omegaWake sampled 601).omega.loops = 2 ∧
    (omegaWake sampled 601).requests.commitments task = .active := by decide

theorem empty_search_is_not_a_universal_absence_certificate :
    searchObservation 7 2 ⟨7, 2, [], false, true⟩ = .unavailable ∧
    searchObservation 7 2 ⟨7, 2, [], true, false⟩ = .unavailable ∧
    searchObservation 7 2 ⟨7, 1, [], true, true⟩ = .unavailable ∧
    searchObservation 7 2 ⟨7, 2, [], true, true⟩ = .absent := by decide

theorem late_broker_result_survives_mode_switch_and_restart :
    let next := report (restore (selectMode proposed .omega)) success
    next.dispatch = none ∧ next.requests.journal = [success] ∧
    next.requests.phase = .awaitingObservation success ∧
    next.requests.commitments task = .active := by decide

/-! Six deliberately broken alternatives; each violates a checked boundary. -/

theorem ignoring_snapshot_revision_admits_stale_effect :
    (reply newInput 0 0 (.command ticket 10)).dispatch = none ∧
    (handleReply newInput 0 captured (.command ticket 10)).dispatch.isSome = true := by decide

theorem clearing_observation_barrier_permits_blind_followup :
    let failed := report proposed failure
    let broken := { failed with requests := { failed.requests with phase := .ready } }
    let followup := ConversationContinuation.Ticket.mk task 2
    (reply (capture failed 0 task []) 0 1 (.command followup 10)).dispatch = none ∧
    (reply (capture broken 0 task []) 0 1 (.command followup 10)).dispatch.isSome = true := by decide

def advertisementOnly (snap : Snapshot) (tool : Nat) : Bool :=
  decide (tool ∈ snap.router.advertised)

theorem trusting_advertisement_grants_missing_authority :
    let snap := snapshot active task
      [fun boundary => some { boundary with advertised := [99] }]
    admitCommand snap ticket 99 = none ∧ advertisementOnly snap 99 = true := by decide

def eraseCommitmentOnNop (state : State) : State :=
  { state with requests := ConversationContinuation.setCommitment state.requests task .inactive }

theorem treating_nop_as_completion_loses_unfinished_work :
    ConversationContinuation.idleAllowed active.requests = false ∧
    ConversationContinuation.idleAllowed (eraseCommitmentOnNop active).requests = true := by decide

def emptyMeansAbsent (report : SearchReport) : Bool := report.hits.isEmpty

theorem empty_hits_alone_misclassify_unavailable_search :
    let unavailable : SearchReport := ⟨7, 2, [], false, false⟩
    searchObservation 7 2 unavailable = .unavailable ∧
    emptyMeansAbsent unavailable = true := by decide

theorem fresh_boot_instead_of_checkpoint_restore_loses_work_and_effects :
    (restore proposed).requests.commitments task = .active ∧
    (restore proposed).requests.issued = [ticket] ∧
    (initial 10).requests.commitments task = .inactive ∧
    (initial 10).requests.issued = [] := by decide

end ObservedStrategyChecks
