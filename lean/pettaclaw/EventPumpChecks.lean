import ChannelJoin
import ReadyQueue
import FairGoalScheduling

/-!
# Pump/channel replays and adversarial alternatives

Positive replays exercise ownership, soft waits, settlement/recovery, selective
receive, persistent joins and the answer/timer race. Negative models deliberately
remove the recheck, fair rotation, time bound or atomic reaction publication.
These check the Lean contract, not the production C/MeTTa implementations.
-/

namespace EventPumpChecks

def owner : EventPump.Key := ⟨7, 2, 9⟩
def foreignOwner : EventPump.Key := ⟨7, 1, 9⟩
def emptyInbox : EventPump.Inbox := { owner }
def input : EventPump.Event := ⟨10, owner, 4⟩
def answer : EventPump.Event := ⟨11, owner, 5⟩
def other : EventPump.Event := ⟨12, foreignOwner, 6⟩

def lifecycle : List EventPump.Action :=
  [.arrival input, .park (EventPump.arm emptyInbox), .claim input.serial,
   .recover, .claim input.serial, .settle input.serial,
   .settle input.serial, .recover]

theorem initial_inbox_satisfies_contract : EventPump.invariant emptyInbox := by
  simp [EventPump.invariant, EventPump.accounted, EventPump.owned,
    EventPump.safeSleep, emptyInbox]

theorem recovery_replay_keeps_one_settlement :
    (EventPump.run lifecycle emptyInbox).phase input.serial = some .settled ∧
    (EventPump.run lifecycle emptyInbox).receipts = [input.serial] := by decide

theorem arbitrary_lifecycle_keeps_evidence (actions : List EventPump.Action) :
    EventPump.invariant (EventPump.run actions emptyInbox) :=
  EventPump.arbitrary_trace_preserves_invariant actions emptyInbox initial_inbox_satisfies_contract

def stutteringHost : EventPump.HostAdapter EventPump.Inbox Unit :=
  { project := id, advance := fun host _ => host, decode := fun _ => none
    refines := by intro _ _; rfl }

/-- Safety refinement alone admits a host that never processes queued work.
Continued service is therefore a separate implementation obligation. -/
theorem safety_refinement_alone_cannot_force_service (slots : Nat) :
    EventPump.hostRun stutteringHost (List.replicate slots ())
      (EventPump.record emptyInbox input) = EventPump.record emptyInbox input := by
  induction slots with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, EventPump.hostRun, stutteringHost] using ih

theorem finite_input_queue_has_a_bounded_disposition_replay :
    EventPump.pending (EventPump.drain 2
      (EventPump.record (EventPump.record emptyInbox input) answer)) = [] := by decide

theorem previous_generation_cannot_enter_mailbox :
    (EventPump.record emptyInbox other).journal = [] := by decide

theorem changed_payload_cannot_overwrite_same_serial :
    (EventPump.record (EventPump.record emptyInbox input) { input with payload := 99 }).journal =
      [input] := by decide

theorem selective_receive_keeps_earlier_unmatched_input :
    let s := EventPump.record (EventPump.record emptyInbox input) answer
    let next := EventPump.receive s (fun e => decide (e.payload = 5))
    next.phase input.serial = some .queued ∧ next.phase answer.serial = some .claimed := by decide

def call : AsyncWait.Call := { id := owner, capturedRevision := 3, sent := true }

theorem slow_call_retains_ownership_without_duplicate_submission :
    (AsyncWait.softWait call).id = owner ∧
    AsyncWait.canSubmit (some (AsyncWait.softWait call)) = false := by decide

theorem late_answer_is_taken_once :
    let completed := AsyncWait.settle (AsyncWait.softWait call) owner (.answer 5)
    let adopted := AsyncWait.adopt completed 3
    (EventPump.takeAnswer completed 3).isSome = true ∧
      EventPump.takeAnswer adopted 3 = none := by decide

theorem restarted_unknown_call_cannot_authorize_actions :
    EventPump.takeAnswer (AsyncWait.recover call) 3 = none := by decide

def blindPark (s : EventPump.Inbox) : EventPump.Inbox := { s with sleeping := true }

theorem missing_recheck_loses_wakeup :
    (blindPark (EventPump.record emptyInbox input)).sleeping = true ∧
    EventPump.pending (blindPark (EventPump.record emptyInbox input)) ≠ [] := by decide

theorem safe_recheck_repairs_same_race :
    (EventPump.park (EventPump.record emptyInbox input) (EventPump.arm emptyInbox)).sleeping = false ∧
    EventPump.pending (EventPump.park (EventPump.record emptyInbox input)
      (EventPump.arm emptyInbox)) = [input] := by decide

def oldServices (slots : Nat) : List Nat := List.replicate slots 0

theorem missing_rotation_starves_second_task (slots : Nat) : 1 ∉ oldServices slots := by
  simp [oldServices]

theorem rotation_serves_despite_new_work :
    EventPump.services 4 (fun n => [100 + n]) [0, 1, 2] = [0, 1, 2, 0] := by decide

theorem retired_head_does_not_skip_waiting_task :
    let first := ReadyQueue.step ⟨2, [0, 1]⟩ .visit
    let removed := ReadyQueue.step first.2 (.remove 0)
    let admitted := ReadyQueue.step removed.2 (.admit 2)
    first.1.visited = some 0 ∧ (ReadyQueue.step admitted.2 .visit).1.visited = some 1 := by decide

/-- Advancing an array cursor before removing slot zero skips the waiter
when a new task fills that slot's former position. -/
theorem advancing_cursor_violates_prefix_bound :
    let original := [0, 1]
    let nextCursor := (0 + 1) % original.length
    let refilled := original.tail ++ [2]
    refilled[nextCursor]? = some 2 ∧ refilled.head? = some 1 := by decide

theorem unbounded_slot_breaks_any_proposed_time_bound (q p : Nat) :
    p + [q + 1].sum > p + 1 * q := by simp

theorem duplicate_wakes_do_not_use_more_slots :
    EventPump.admit 2 [owner] owner = some [owner] ∧
    EventPump.admit 1 [owner] foreignOwner = none := by decide

/-- The event pump need not replace the existing weighted goal policy. -/
theorem weighted_goal_service_reuses_existing_contract (goals : List GoalSystem.Goal)
    (target : GoalSystem.Goal) (member : target ∈ goals)
    (runnable : FairGoalScheduling.runnable target = true) :
    target.id ∈ FairGoalScheduling.trace (FairGoalScheduling.waitBudget target goals + 1) goals :=
  FairGoalScheduling.no_starvation goals target member runnable

def pattern (channel : EventPump.Key) (payload : Nat) : ChannelJoin.Pattern :=
  ⟨channel, fun value => decide (value = payload)⟩

def join : ChannelJoin.Continuation := { patterns := [pattern owner 4, pattern owner 5] }
def joinedSpace : ChannelJoin.Space :=
  ChannelJoin.register
    (ChannelJoin.produce (ChannelJoin.produce {} input) answer) 20 join

theorem partial_join_is_rejected :
    ¬ ChannelJoin.valid joinedSpace join [input] := by decide

theorem complete_join_publishes_owned_tuple :
    (ChannelJoin.commit joinedSpace 20 [input, answer]).available = [] ∧
    (ChannelJoin.commit joinedSpace 20 [input, answer]).ready = [⟨20, [input, answer]⟩] ∧
    (ChannelJoin.commit joinedSpace 20 [input, answer]).receives 20 = none := by decide

def samePayload : EventPump.Event := { input with serial := 13 }
def twice : ChannelJoin.Continuation := { patterns := [pattern owner 4, pattern owner 4] }
def twoOccurrences : ChannelJoin.Space :=
  ChannelJoin.register (ChannelJoin.produce (ChannelJoin.produce {} input) samePayload) 21 twice

theorem equal_payloads_still_require_distinct_occurrences :
    ¬ ChannelJoin.valid twoOccurrences twice [input, input] ∧
    ChannelJoin.valid twoOccurrences twice [input, samePayload] := by decide

def persistent : ChannelJoin.Continuation := { patterns := [pattern owner 4], persistent := true }
def persistentTrace : ChannelJoin.Space :=
  ChannelJoin.run [.produce input, .register 22 persistent, .react 22 [input],
    .react 22 [input], .produce samePayload, .react 22 [samePayload]] {}

theorem persistent_receiver_requires_fresh_sends :
    persistentTrace.ready = [⟨22, [input]⟩, ⟨22, [samePayload]⟩] ∧
    persistentTrace.available = [] := by decide

def halfCommit : ChannelJoin.Space := { joinedSpace with available := [] }

theorem removing_sends_before_publishing_reaction_loses_work :
    ¬ ChannelJoin.conserved halfCommit := by
  intro conservation
  have lost := conservation input (by simp [halfCommit, joinedSpace,
    ChannelJoin.register, ChannelJoin.produce, input, answer])
  simp [halfCommit, joinedSpace, ChannelJoin.register, ChannelJoin.produce, input, answer] at lost

def latch : EventPump.Event := ⟨14, ⟨7, 2, 10⟩, 0⟩
def tick : EventPump.Event := ⟨15, ⟨7, 2, 11⟩, 0⟩
def answerArm : ChannelJoin.Continuation :=
  { patterns := [pattern answer.owner answer.payload, pattern latch.owner 0] }
def timerArm : ChannelJoin.Continuation :=
  { patterns := [pattern tick.owner 0, pattern latch.owner 0] }
def lateArm : ChannelJoin.Continuation :=
  { patterns := [pattern answer.owner answer.payload] }
def race : ChannelJoin.Space :=
  ChannelJoin.run [.produce answer, .produce latch, .produce tick,
    .register 30 answerArm, .register 31 timerArm] {}

theorem answer_timer_latch_has_one_winner_in_both_orders :
    (ChannelJoin.commit (ChannelJoin.commit race 30 [answer, latch]) 31 [tick, latch]).ready.length = 1 ∧
    (ChannelJoin.commit (ChannelJoin.commit race 31 [tick, latch]) 30 [answer, latch]).ready.length = 1 := by decide

theorem timer_winner_can_still_receive_late_answer :
    let timed := ChannelJoin.commit race 31 [tick, latch]
    let resumed := ChannelJoin.commit (ChannelJoin.register timed 32 lateArm) 32 [answer]
    answer ∈ timed.available ∧
    resumed.ready = [⟨31, [tick, latch]⟩, ⟨32, [answer]⟩] := by decide

theorem arbitrary_channel_lifecycle_keeps_all_inputs (actions : List ChannelJoin.Action) :
    ChannelJoin.conserved (ChannelJoin.run actions {}) :=
  ChannelJoin.arbitrary_channel_trace_conserves_occurrences {} actions (by
    simp [ChannelJoin.conserved])

end EventPumpChecks
