import TopicAsync
import FairGoalStrategy

namespace TopicAsyncChecks

open TopicAsync
open Mettapedia.CogArch.Agent

def key (id round : Nat) : ConversationContinuation.RequestKey := ⟨7, round, id⟩
def cfg : Config :=
  { goals := ⟨fun pair => key pair.1 pair.2, by
      intro a b same
      cases a; cases b
      simp [key, ConversationContinuation.RequestKey.mk.injEq] at same
      exact Prod.ext same.2 same.1⟩
    topicForGoal := id }

def goalA : GoalSystem.Goal := { id := 1 }
def goalB : GoalSystem.Goal := { id := 2 }
def taskA := key 1 0
def taskB := key 2 0

def initial : State :=
  { core := { agent := { ObservedStrategy.initial 10 with
                           router := ⟨[10], [10], [10]⟩ }
              goals := [goalA, goalB] }
    contexts := fun _ => {}
    owners := fun _ => none
    agentId := 7
    maxCalls := 2
    maxBytes := 128 }

def ready : State := acknowledge (deliver (acknowledge (deliver initial 1 taskA) taskA) 2 taskB) taskB
def sampledA : State := capture cfg ready 0 goalA [] [] 64
def sampledAB : State := capture cfg sampledA 0 goalB [] [] 64
def callA : CallId := ⟨7, 0, 0⟩
def callB : CallId := ⟨7, 0, 1⟩
def ticketA : ConversationContinuation.Ticket := ⟨taskA, 1⟩

theorem another_topic_runs_while_one_waits :
    sampledAB.calls.length = 2 ∧ sampledAB.core.agent.allowance = 8 ∧
    sampledAB.core.goals.map GoalSystem.Goal.service = [1, 1] := by decide

theorem inactive_queue_entry_does_not_block_an_accepted_peer :
    let onlyB := acknowledge (deliver initial 2 taskB) taskB
    let sampled := capture cfg onlyB 0 goalB [] [] 64
    sampled.calls.map (fun slot => slot.call.topic) = [2] ∧
      sampled.core.goals.map GoalSystem.Goal.service = [0, 1] := by decide

theorem reversed_arrivals_keep_their_original_topics :
    let arrived := receive (receive sampledAB callB (.text 22) 30) callA (.text 11) 31
    arrived.calls.map (fun slot => (slot.call.topic, slot.phase)) =
      [(1, .terminal (.text 11)), (2, .terminal (.text 22))] := by decide

theorem duplicate_and_foreign_results_do_not_rewrite_evidence :
    let arrived := receive sampledAB callA (.text 11) 31
    let duplicate := receive arrived callA (.text 99) 31
    let foreign := receive duplicate ⟨8, 0, 0⟩ (.text 66) 31
    foreign.calls = arrived.calls ∧ foreign.core.agent.allowance = 8 := by decide

theorem partial_content_cannot_dispatch_or_complete :
    let provisional := issue (observe (progress sampledAB callA 20) callA) 0 callA
    provisional.core.agent.dispatch = none ∧
    provisional.core.agent.requests.commitments taskA = .active ∧
    provisional.calls.head?.map Slot.phase = some .waiting := by decide

theorem provider_observation_precedes_dispatch :
    let arrived := receive sampledAB callA (.command ticketA 10) 20
    (issue arrived 0 callA).core.agent.dispatch = none ∧
    (issue (observe arrived callA) 0 callA).core.agent.dispatch.isSome = true := by decide

theorem own_topic_changes_block_old_proposals :
    let arrived := observe (receive sampledAB callA (.command ticketA 10) 20) callA
    (issue (changed arrived 1) 0 callA).core.agent.dispatch = none := by decide

theorem unrelated_topic_changes_keep_independent_proposals_valid :
    let arrived := observe (receive sampledAB callA (.command ticketA 10) 20) callA
    (issue (changed arrived 2) 0 callA).core.agent.dispatch.isSome = true := by decide

theorem declared_shared_dependency_changes_block_old_proposals :
    let sampled := capture cfg ready 0 goalA [] [2] 64
    let arrived := observe (receive sampled callA (.command ticketA 10) 20) callA
    (issue (changed arrived 2) 0 callA).core.agent.dispatch = none := by decide

theorem saturation_refuses_additional_attempts_without_charge :
    let extra := capture cfg sampledAB 0 goalA [] [] 64
    extra.calls = sampledAB.calls ∧ extra.core.agent.allowance = 8 := by decide

theorem storage_reservation_applies_across_topics :
    let tight := { sampledA with maxBytes := 100 }
    let extra := capture cfg tight 0 goalB [] [] 64
    extra.calls = sampledA.calls ∧ extra.core.agent.allowance = 9 := by decide

theorem oversize_terminal_is_failure_evidence :
    (receive sampledAB callA (.text 11) 65).calls.head?.map Slot.phase =
      some (.terminal (.failure 1 1)) := by decide

theorem restart_retains_uncertainty_and_accepts_only_stale_late_evidence :
    let recovered := restore sampledAB
    let late := observe (receive recovered callA (.command ticketA 10) 20) callA
    recovered.calls.map Slot.phase = [.uncertain, .uncertain] ∧
    recovered.core.agent.allowance = 8 ∧
    (issue late 0 callA).core.agent.dispatch = none ∧
    late.calls.head?.map Slot.phase = some (.terminal (.command ticketA 10)) := by decide

theorem retirement_waits_for_observation :
    let arrived := receive sampledAB callA (.text 11) 31
    (retire arrived callA).calls.length = 2 ∧
    (retire (observe arrived callA) callA).calls.length = 1 := by decide


def ticketB : ConversationContinuation.Ticket := ⟨taskB, 1⟩

theorem provider_parallelism_keeps_tools_serialized :
    let results := observe (observe (receive (receive sampledAB callA
      (.command ticketA 10) 20) callB (.command ticketB 10) 20) callA) callB
    let first := issue results 0 callA
    let second := issue first 0 callB
    second.core.agent.dispatch.map (fun dispatch => dispatch.ticket) = some ticketA ∧
      second.core.agent.requests.issued = [ticketA] := by decide

theorem unresolved_effect_does_not_freeze_an_unoccupied_topic :
    let arrived := observe (receive sampledA callA (.command ticketA 10) 20) callA
    let dispatched := issue arrived 0 callA
    let peer := capture cfg dispatched 0 goalB [] [] 64
    peer.calls.length = 2 ∧ peer.core.agent.allowance = 8 ∧
    peer.core.agent.dispatch.map (fun dispatch => dispatch.ticket) = some ticketA ∧
    peer.core.agent.requests.issued = [ticketA] := by decide

theorem peer_completion_cannot_overwrite_an_unresolved_effect :
    let arrived := observe (receive sampledA callA (.command ticketA 10) 20) callA
    let dispatched := issue arrived 0 callA
    let peer := capture cfg dispatched 0 goalB [] [] 64
    let answered := observe (receive peer callB (.command ticketB 10) 20) callB
    let attempted := issue answered 0 callB
    attempted.core.agent.dispatch.map (fun dispatch => dispatch.ticket) = some ticketA ∧
    attempted.core.agent.requests.issued = [ticketA] ∧
    attempted.calls.getLast?.map Slot.handled = some false := by decide

theorem failures_apply_cooldown_before_retirement :
    let arrived := observe (receive sampledA callA (.failure 429 100) 20) callA
    let handled := retire (issue arrived 4 callA) callA
    (retire arrived callA).calls.length = 1 ∧ handled.calls.isEmpty = true ∧
    handled.core.agent.cooldownUntil = 104 ∧
    (capture cfg handled 10 goalB [] [] 64).calls.isEmpty = true ∧
    (capture cfg handled 104 goalB [] [] 64).calls.length = 1 := by decide

theorem duplicate_command_cannot_replay_an_effect :
    let arrived := observe (receive sampledA callA (.command ticketA 10) 20) callA
    let first := issue arrived 0 callA
    (issue first 0 callA).core.agent.requests.issued = [ticketA] ∧
      (issue first 0 callA).core.agent.decisions = first.core.agent.decisions := by decide

theorem old_single_call_path_cannot_bypass_the_pool :
    (control sampledAB (.captured 0 taskA [])).calls = sampledAB.calls ∧
    (control sampledAB (.captured 0 taskA [])).core.agent.allowance = 8 ∧
    (control sampledAB .restarted).calls.map Slot.phase = [.uncertain, .uncertain] := by decide

theorem retired_identity_cannot_consume_a_new_generation :
    let recovered := restore sampledA
    let reconciled := retire (issue (observe (receive recovered callA (.failure 1 1) 20) callA) 0 callA) callA
    let next := capture cfg reconciled 1 goalB [] [] 64
    next.calls.map (fun slot => slot.call.id) = [⟨7, 1, 1⟩] ∧
    (receive next callA (.text 99) 20).calls = next.calls := by decide

/-! Deliberately broken alternatives: each violates a stated contract. -/

def brokenForegroundRouting (state : State) (id : CallId) (foreground : Topic) : State :=
  mapSlot state id fun slot => { slot with call := { slot.call with topic := foreground } }

theorem foreground_routing_loses_original_owner :
    (brokenForegroundRouting sampledAB callA 2).calls.map (fun slot => slot.call.topic) = [2, 2] ∧
    (receive sampledAB callA (.text 11) 20).calls.map (fun slot => slot.call.topic) = [1, 2] := by decide

def brokenSkipObservation (state : State) (now : Int) (id : CallId) : State :=
  issue (mapSlot state id fun slot => { slot with observed := true }) now id

theorem skipped_observation_initiates_an_unobserved_effect :
    let arrived := receive sampledA callA (.command ticketA 10) 20
    (brokenSkipObservation arrived 0 callA).core.agent.dispatch.isSome = true ∧
    (issue arrived 0 callA).core.agent.dispatch = none := by decide

def brokenIgnoreDependencies (state : State) (now : Int) (id : CallId) : State :=
  issue (mapSlot state id fun slot => { slot with call := { slot.call with dependencies := [] } }) now id

theorem ignoring_dependencies_admits_a_stale_shared_read :
    let sampled := capture cfg ready 0 goalA [] [2] 64
    let arrived := changed (observe (receive sampled callA (.command ticketA 10) 20) callA) 2
    (brokenIgnoreDependencies arrived 0 callA).core.agent.dispatch.isSome = true ∧
    (issue arrived 0 callA).core.agent.dispatch = none := by decide

def brokenOversizeAdmission (state : State) (id : CallId) (bytes : Nat) : State :=
  receive (mapSlot state id fun slot => { slot with call := { slot.call with reservedBytes := bytes } })
    id (.text 11) bytes

theorem bypassing_reservations_exceeds_the_shared_limit :
    retainedBytes (brokenOversizeAdmission sampledAB callA 129).calls > sampledAB.maxBytes ∧
    (receive sampledAB callA (.text 11) 129).calls.head?.map Slot.phase =
      some (.terminal (.failure 1 1)) := by decide

def brokenRestartDropsWork (state : State) : State :=
  { restore state with core := { (restore state).core with
    agent := { (restore state).core.agent with requests := ConversationContinuation.initial } } }

theorem dropping_checkpoint_state_loses_accepted_work :
    (brokenRestartDropsWork sampledAB).core.agent.requests.commitments taskA = .inactive ∧
      (restore sampledAB).core.agent.requests.commitments taskA = .active := by decide

def brokenForgetBeforeTerminal (state : State) (id : CallId) : State :=
  { state with calls := state.calls.filter fun slot => decide (slot.call.id ≠ id) }

theorem forgetting_a_slow_call_loses_late_evidence :
    (receive (brokenForgetBeforeTerminal sampledA callA) callA (.text 11) 20).calls = [] ∧
      (receive (softWait sampledA) callA (.text 11) 20).calls.head?.map Slot.phase =
        some (.terminal (.text 11)) := by decide


/-! Complete effect feedback before goal completion, using the original checker. -/

def successA : ConversationContinuation.Receipt :=
  ⟨ticketA, ⟨.returned, .success⟩, 42⟩
def acceptsA (key : ConversationContinuation.RequestKey) (receipt : ConversationContinuation.Receipt) : Bool :=
  decide (key = taskA ∧ receipt.payload = 42)
def effectedA : State :=
  retire (issue (observe (receive sampledA callA (.command ticketA 10) 20) callA) 0 callA) callA
def checkedA : State := control (control effectedA (.reported successA)) (.observed ticketA)
def reportA : GoalSystem.Report := ⟨1, 1, successA⟩

theorem successful_observed_effect_completes_only_its_checked_goal :
    let finished := completeCycle cfg acceptsA checkedA reportA
    finished.core.agent.requests.commitments taskA = .discharged ⟨.achieved, .result successA⟩ ∧
    finished.core.agent.requests.commitments taskB = .active ∧
    finished.core.goals.map GoalSystem.Goal.finished = [true, false] ∧
    finished.core.goals.map GoalSystem.Goal.service = [1, 0] := by decide

theorem provider_text_cannot_pay_a_completion_receipt :
    let answered := retire (observe (receive sampledA callA (.text 42) 20) callA) callA
    (completeCycle cfg acceptsA answered { reportA with revision := 0 }).core.agent.requests.commitments taskA =
      .active := by decide

theorem mode_change_rejects_authority_without_losing_evidence :
    let arrived := observe (receive sampledAB callA (.command ticketA 10) 20) callA
    let switched := control arrived (.modeSelected .iter)
    (issue switched 0 callA).core.agent.dispatch = none ∧
    switched.calls.head?.map Slot.phase = some (.terminal (.command ticketA 10)) ∧
    switched.core.agent.requests.commitments taskA = .active := by decide

end TopicAsyncChecks
