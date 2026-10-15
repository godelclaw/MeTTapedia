import Mettapedia.Machines.ChannelJoin
import Mettapedia.Machines.ReadyQueue
import Mettapedia.Machines.Cursor.FairObservation

/-!
# Pump/channel replays and adversarial alternatives

Positive replays exercise ownership, soft waits, settlement/recovery, selective
receive, persistent joins and the answer/timer race. Negative models deliberately
remove the recheck, fair rotation, time bound or atomic reaction publication.
These check the Lean contract, not the production C/MeTTa implementations.
-/

namespace Mettapedia.Machines.EventPumpControls

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
    CooperativeQueue.services 4 (fun n => [100 + n]) [0, 1, 2] = [0, 1, 2, 0] := by decide

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

/-- Two distinct message occurrences on one channel may serve different
receivers without requiring a channel-wide serial dependency. -/
def disjointJoins : ChannelJoin.Space :=
  ChannelJoin.run [.produce input, .produce samePayload,
    .register 23 persistent, .register 24 { persistent with persistent := false }] {}

theorem same_channel_disjoint_resources_fit :
    ((ChannelJoin.joinDemand 23 persistent [input]).reserve
      (ChannelJoin.joinDemand 24 { persistent with persistent := false } [samePayload]).consume
      (ChannelJoin.joinDemand 24 { persistent with persistent := false } [samePayload]).read).Fits
        (ChannelJoin.resourceSnapshot disjointJoins).val := by decide

theorem shared_persistent_receiver_resources_fit :
    ((ChannelJoin.joinDemand 23 persistent [input]).reserve
      (ChannelJoin.joinDemand 23 persistent [samePayload]).consume
      (ChannelJoin.joinDemand 23 persistent [samePayload]).read).Fits
        (ChannelJoin.resourceSnapshot disjointJoins).val := by decide

theorem one_shot_receiver_resources_conflict :
    ¬ ((ChannelJoin.joinDemand 24 { persistent with persistent := false } [input]).reserve
      (ChannelJoin.joinDemand 24 { persistent with persistent := false } [samePayload]).consume
      (ChannelJoin.joinDemand 24 { persistent with persistent := false } [samePayload]).read).Fits
        (ChannelJoin.resourceSnapshot disjointJoins).val := by decide

theorem repeated_send_resources_conflict :
    ¬ ((ChannelJoin.joinDemand 23 persistent [input]).reserve
      (ChannelJoin.joinDemand 23 persistent [input]).consume
      (ChannelJoin.joinDemand 23 persistent [input]).read).Fits
        (ChannelJoin.resourceSnapshot disjointJoins).val := by decide

/-- Claim multiplicity survives extraction, including a repeated occurrence
inside a single candidate. The snapshot cannot license it twice. -/
theorem duplicate_candidate_resources_conflict :
    ¬ (ChannelJoin.joinDemand 21 twice [input, input]).Fits (ChannelJoin.resourceSnapshot twoOccurrences).val := by decide

/-- A fitting footprint alone cannot authorize a reaction: it does not
establish the arity, channel or payload requirements of its patterns. -/
theorem resource_admission_does_not_validate_partial_match :
    (ChannelJoin.joinDemand 20 join [input]).Fits (ChannelJoin.resourceSnapshot joinedSpace).val ∧
      ¬ ChannelJoin.valid joinedSpace join [input] := by decide

/-- Resource reservation is not publication. A partial candidate changes no
store resources, even when its footprint would fit. -/
theorem partial_join_does_not_spend_reserved_resources :
    ChannelJoin.resourceSnapshot (ChannelJoin.commit joinedSpace 20 [input]) =
        ChannelJoin.resourceSnapshot joinedSpace ∧
    (ChannelJoin.resourceSnapshot (ChannelJoin.commit joinedSpace 20 [input])).val ≠
      (ChannelJoin.resourceSnapshot joinedSpace).val -
        (ChannelJoin.joinDemand 20 join [input]).consume := by decide

theorem same_channel_disjoint_joins_preserve_occurrences :
    let forward := ChannelJoin.commit (ChannelJoin.commit disjointJoins 23 [input]) 24 [samePayload]
    let reverse := ChannelJoin.commit (ChannelJoin.commit disjointJoins 24 [samePayload]) 23 [input]
    forward.available = reverse.available ∧
    forward.ready.Perm reverse.ready ∧
    forward.receives 23 = some persistent ∧ forward.receives 24 = none := by
  have commuting := ChannelJoin.admitted_joins_commute_modulo_publication_order
    disjointJoins 23 24 persistent { persistent with persistent := false } [input] [samePayload]
    (by rfl) (by rfl) (by decide) (by decide) (by decide) (by decide)
    same_channel_disjoint_resources_fit
  exact ⟨commuting.2.1, commuting.2.2.2.2.2, by rfl, by rfl⟩

/-- A persistent receiver can serve disjoint occurrences in either order;
its identity need not force a serial dependency between these reactions. -/
theorem persistent_receiver_admits_disjoint_reactions :
    let forward := ChannelJoin.commit (ChannelJoin.commit disjointJoins 23 [input]) 23 [samePayload]
    let reverse := ChannelJoin.commit (ChannelJoin.commit disjointJoins 23 [samePayload]) 23 [input]
    forward.available = reverse.available ∧ forward.ready.Perm reverse.ready ∧
    forward.receives 23 = some persistent := by
  have commuting := ChannelJoin.admitted_joins_commute_modulo_publication_order
    disjointJoins 23 23 persistent persistent [input] [samePayload]
    (by rfl) (by rfl) (by decide) (by decide) (by decide) (by decide)
    shared_persistent_receiver_resources_fit
  exact ⟨commuting.2.1, commuting.2.2.2.2.2, by rfl⟩

/-- Erasing publication order is an observation choice, not equality of the
actual ready queues. A stream observer can distinguish these schedules. -/
theorem disjoint_joins_do_not_preserve_ordered_delivery :
    (ChannelJoin.commit (ChannelJoin.commit disjointJoins 23 [input]) 24 [samePayload]).ready ≠
      (ChannelJoin.commit (ChannelJoin.commit disjointJoins 24 [samePayload]) 23 [input]).ready := by
  decide

/-- Disjoint sends are insufficient when both firings claim one one-shot
receiver. Its identity is also a consumed resource. -/
theorem one_shot_receiver_prevents_disjoint_send_reordering :
    (ChannelJoin.commit (ChannelJoin.commit disjointJoins 24 [input]) 24 [samePayload]).available ≠
      (ChannelJoin.commit (ChannelJoin.commit disjointJoins 24 [samePayload]) 24 [input]).available := by
  decide

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

theorem shared_latch_resources_conflict :
    ¬ ((ChannelJoin.joinDemand 30 answerArm [answer, latch]).reserve
      (ChannelJoin.joinDemand 31 timerArm [tick, latch]).consume
      (ChannelJoin.joinDemand 31 timerArm [tick, latch]).read).Fits
        (ChannelJoin.resourceSnapshot race).val := by decide

theorem answer_timer_latch_has_one_winner_in_both_orders :
    (ChannelJoin.commit (ChannelJoin.commit race 30 [answer, latch]) 31 [tick, latch]).ready.length = 1 ∧
    (ChannelJoin.commit (ChannelJoin.commit race 31 [tick, latch]) 30 [answer, latch]).ready.length = 1 := by decide

/-- The shared latch changes which continuation is published, even if an
observer forgets publication order. These joins cannot share an admitted wave. -/
theorem shared_latch_changes_even_unordered_reactions :
    ¬ (ChannelJoin.commit (ChannelJoin.commit race 30 [answer, latch]) 31 [tick, latch]).ready.Perm
      (ChannelJoin.commit (ChannelJoin.commit race 31 [tick, latch]) 30 [answer, latch]).ready := by
  decide

theorem timer_winner_can_still_receive_late_answer :
    let timed := ChannelJoin.commit race 31 [tick, latch]
    let resumed := ChannelJoin.commit (ChannelJoin.register timed 32 lateArm) 32 [answer]
    answer ∈ timed.available ∧
    resumed.ready = [⟨31, [tick, latch]⟩, ⟨32, [answer]⟩] := by decide

theorem arbitrary_channel_lifecycle_keeps_all_inputs (actions : List ChannelJoin.Action) :
    ChannelJoin.conserved (ChannelJoin.run actions {}) :=
  ChannelJoin.arbitrary_channel_trace_conserves_occurrences {} actions (by
    simp [ChannelJoin.conserved])

section RetainedObservation

open Cursor Cursor.Scheduling Cursor.FairObservation
open Mettapedia.GSLT.LanguageDef
open NativeControlEffectCursor (provider)
open NativeControlBoundedCursor (client packet)

/-- The event wakes a real bounded observer of an infinite source. Subsequent
arrivals do not change its three answers, three paid pulls or unpolled tail. -/
theorem awakened_ongoing_source_delivers_exact_prefix :
    let pull := streamPull (World := Unit) (fun n : Nat => n)
    let pool : Pool (provider pull) (client Nat) EventPump.Key () :=
      fun _ => (0, .paused (packet pull 3 5 () []))
    ∃ slots, ∀ extra,
      execute (provider pull) (client Nat) (fun _ _ => 1)
        (cooperativeSchedule 1 (slots + extra) (fun n => [⟨8, 0, n⟩])
          (EventPump.wakeReady [] (EventPump.record emptyInbox input))) pool owner =
        (3, .done ⟨(), ⟨0, .limit, [5, 6, 7]⟩, (8, ())⟩) := by
  dsimp only
  apply accepted_eventually_done _ _ _ emptyInbox input (by decide) 1 (by decide)
    (fun n => [⟨8, 0, n⟩]) [] _ 4
  simpa [resume, Mettapedia.GSLT.Core.SearchStreamProductivity.streamPrefix] using
    stream_client_exact (World := Unit) (fun n : Nat => n) 3 5 ()

/-- Unequal positive budgets serve the finite observer, despite new arrivals.
It retires on its second visit, retains the unpolled source tail, and incurs
only its three pulls even though its final budget exceeds the work needed. -/
theorem unequal_budgets_finish_before_retirement :
    let keep := fun n : Nat => decide (n ≠ 2)
    let offered := fun n : Nat => [n + 2]
    let state : ReadyQueue.State := ⟨2, [0, 1]⟩
    let pull := streamPull (World := Unit) (fun n : Nat => n)
    let pool : Pool (provider pull) (client Nat) Nat () :=
      fun _ => (0, .paused (packet pull 3 5 () []))
    0 ∉ (ReadyQueue.serviceRun 4 keep offered state).2.tasks ∧
    execute (provider pull) (client Nat) (fun _ _ => 1)
      [(0, 2), (1, 0), (0, 5), (1, 1)] pool 0 =
        (3, .done ⟨(), ⟨0, .limit, [5, 6, 7]⟩, (8, ())⟩) := by
  dsimp only
  refine ⟨by decide, ?_⟩
  have retained : ∀ n,
      (ReadyQueue.serviceRun (n + 1) (fun n => decide (n ≠ 2))
        (fun n => [n + 2]) ⟨2, [0, 1]⟩).1.count 0 < 2 →
      (ReadyQueue.serviceRun n (fun n => decide (n ≠ 2))
        (fun n => [n + 2]) ⟨2, [0, 1]⟩).2.tasks.head? = some 0 →
      decide (n ≠ 2) = true := by
    intro n short _
    by_cases lastVisit : n = 2
    · subst n
      have count : (ReadyQueue.serviceRun 3 (fun n => decide (n ≠ 2))
          (fun n => [n + 2]) ⟨2, [0, 1]⟩).1.count 0 = 2 := by decide
      rw [count] at short
      omega
    · simp [lastVisit]
  apply ready_variable_observation_before_retirement _ _ _ 2 2 0
    ⟨2, [0, 1]⟩ 0 (fun n => decide (n ≠ 2)) (fun n => [n + 2])
    (by change [0, 1].Nodup ∧ 2 ≤ 2; decide) (by decide) retained _ (by decide) _ 4
  case finished =>
    simpa [resume, Mettapedia.GSLT.Core.SearchStreamProductivity.streamPrefix] using
      stream_client_exact (World := Unit) (fun n : Nat => n) 3 5 ()
  case enough => decide

/-- A queue visit is not progress for its owner if dispatch silently uses
another identity. The same total budgets cannot repair this lost alignment. -/
theorem wrong_dispatch_owner_loses_all_progress :
    let pull := streamPull (World := Unit) (fun n : Nat => n)
    let pool : Pool (provider pull) (client Nat) Nat () :=
      fun _ => (0, .paused (packet pull 3 5 () []))
    allocation 0 [(1, 2), (1, 0), (1, 5), (1, 1)] = 0 ∧
    execute (provider pull) (client Nat) (fun _ _ => 1)
      [(1, 2), (1, 0), (1, 5), (1, 1)] pool 0 = pool 0 := by
  constructor <;> rfl

end RetainedObservation

open ChannelJoin

def thirdInput : EventPump.Event := { input with serial := 14 }

def waveSpace : Space := produce disjointJoins thirdInput

def waveCandidates : List joinResources.Entry :=
  [⟨(23 : Nat), persistent, [input]⟩,
   ⟨(24 : Nat), { persistent with persistent := false }, [input]⟩,
   ⟨(23 : Nat), persistent, [samePayload]⟩,
   ⟨(24 : Nat), { persistent with persistent := false }, [thirdInput]⟩]

theorem wave_candidates_match_independently :
    ∀ entry ∈ waveCandidates, candidateMatches waveSpace entry := by
  intro entry member
  simp only [waveCandidates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl, by decide⟩

/-- The conflicting occurrence stays deferred; two persistent receives may
share the same receiver while a third tuple uses a one-shot receiver. -/
theorem wave_selects_three_and_retains_conflict :
    let selected := joinResources.selectWave (resourceSnapshot waveSpace).val waveCandidates
    selected.1.map candidateReaction =
      [⟨23, [input]⟩, ⟨23, [samePayload]⟩, ⟨24, [thirdInput]⟩] ∧
    selected.2.map candidateReaction = [⟨24, [input]⟩] := by decide

/-- The finite-wave theorem, applied to reverse publication, preserves the
whole input tuple and every occurrence instead of only its payload values. -/
theorem reverse_wave_preserves_resources_and_exact_queue :
    let selected := (joinResources.selectWave (resourceSnapshot waveSpace).val waveCandidates).1
    (resourceSnapshot (run (selected.reverse.map candidateAction) waveSpace)).val =
      joinResources.waveTarget (resourceSnapshot waveSpace).val selected ∧
    (run (selected.reverse.map candidateAction) waveSpace).ready =
      waveSpace.ready ++ selected.reverse.map candidateReaction :=
  selected_wave_every_order waveSpace waveCandidates _ wave_candidates_match_independently
    (List.reverse_perm _).symm

/-- Treating all individually valid matches as an admitted batch loses a
claimed reaction: the same send cannot satisfy both first and second entries. -/
theorem individual_matches_do_not_license_whole_wave :
    ¬ joinResources.StepEnables (resourceSnapshot waveSpace).val waveCandidates ∧
    (run (waveCandidates.map candidateAction) waveSpace).ready.length = 3 ∧
    waveCandidates.length = 4 := by decide

open ChannelJoin Mettapedia.GSLT.Causality.OccurrenceHistory

/-- Equal payloads remain separate inputs in the history account. The
three admitted reactions each contribute their one actual input occurrence. -/
theorem wave_history_counts_all_three_inputs :
    let selected := (joinResources.selectWave (resourceSnapshot waveSpace).val waveCandidates).1
    ∃ history : OccurrencePath joinResources.presentation (resourceSnapshot waveSpace).val
        (joinResources.waveTarget (resourceSnapshot waveSpace).val selected),
      joinResources.pathEntries history = selected ∧
      (joinResources.instanceValuation (fun candidate => candidate.2.length)).onPath history = 3 := by
  obtain ⟨history, entries, _, _, account⟩ := selected_wave_occurrence_account
    (fun _ candidate => candidate.2.length) waveSpace waveCandidates _
    wave_candidates_match_independently (List.Perm.refl _)
  refine ⟨history, entries, ?_⟩
  rw [account]
  decide

end Mettapedia.Machines.EventPumpControls
