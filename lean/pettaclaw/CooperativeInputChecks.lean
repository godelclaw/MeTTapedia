import CooperativeInput
import TopicAsyncChecks

namespace CooperativeInputChecks
open CooperativeInput

def initial : State := { core := TopicAsyncChecks.sampledAB }
def arrival : Arrival := ⟨TopicAsyncChecks.key 3 0, 1⟩
def peer : Arrival := ⟨TopicAsyncChecks.key 4 0, 2⟩
def notice : Notice := ⟨arrival.key, 7, 10, 42⟩
def ready : State := { core := TopicAsyncChecks.ready }

theorem new_input_keeps_two_calls_alive :
    (enqueue initial arrival).core.calls.length = 2 ∧
    (enqueue initial arrival).waiting = [arrival] := by decide

theorem ordinary_input_preserves_current_foreground :
    let call := (TopicAsyncChecks.sampledA.calls[0]).call
    TopicAsync.current (enqueue initial arrival).core call = true := by decide

theorem correction_invalidates_only_its_declared_region :
    let a := (TopicAsyncChecks.sampledA.calls[0]).call
    let b := (TopicAsyncChecks.sampledAB.calls[1]).call
    TopicAsync.current (steer initial arrival).core a = false ∧
    TopicAsync.current (steer initial arrival).core b = true := by decide

theorem stop_suspends_without_erasing_arrivals_or_calls :
    let suspended := stopped (enqueue initial arrival)
    suspended.waiting = [arrival] ∧ suspended.core.calls.length = 2 ∧
    available suspended = false := by decide

theorem fifo_reaches_two_messages_at_two_boundaries :
    let queued := enqueue (enqueue ready arrival) peer
    (attentionTrace 2 queued).waiting = [] ∧
    (attentionTrace 2 queued).attended = [arrival.key, peer.key] := by decide

theorem resume_restores_attention_to_retained_input :
    let queued := stopped (enqueue ready arrival)
    (attend (resumed queued)).waiting = [] ∧
    (attend (resumed queued)).attended = [arrival.key] := by decide

def noticed : State := registerNotice (enqueue ready arrival) notice
def attended : State := attend noticed
def processed : State := settle attended arrival.key true true

theorem receipt_waits_for_success_and_durable_history :
    deletable attended notice = false ∧
    deletable (settle attended arrival.key false true) notice = false ∧
    deletable (settle attended arrival.key true false) notice = false ∧
    deletable processed notice = true := by decide

theorem processing_is_not_task_completion :
    processed.core.core.agent.requests.commitments arrival.key = .active := by decide

theorem unknown_or_foreign_notice_is_never_deleted :
    deletable processed { notice with message := 43 } = false ∧
    deletable (registerNotice processed { notice with owner := 8 })
      { notice with owner := 8 } = false := by decide

theorem failed_cleanup_and_restart_keep_reconciliation_data :
    (restart (deleted processed notice false)).notices = [notice] ∧
    (restart processed).processed = [arrival.key] := by decide

theorem successful_cleanup_changes_only_its_receipt :
    (deleted processed notice true).notices = [] ∧
    (deleted processed notice true).processed = [arrival.key] ∧
    (deleted processed notice true).core.core.agent.requests.commitments arrival.key = .active := by decide

def results : State :=
  { initial with core := (TopicAsync.observe
    (TopicAsync.observe (TopicAsync.receive
      (TopicAsync.receive initial.core TopicAsyncChecks.callB (.text 22) 10)
      TopicAsyncChecks.callA (.text 11) 10) TopicAsyncChecks.callA) TopicAsyncChecks.callB) }

theorem independent_strands_merge_after_review :
    (adopt (adopt results TopicAsyncChecks.callA true) TopicAsyncChecks.callB true).adopted =
      [TopicAsyncChecks.callA, TopicAsyncChecks.callB] := by decide

theorem duplicate_copies_supply_one_evidence_identity :
    (adopt (adopt results TopicAsyncChecks.callA true) TopicAsyncChecks.callA true).adopted =
      [TopicAsyncChecks.callA] := by decide

theorem stale_result_stays_available_but_cannot_merge :
    let stale := steer results arrival
    (adopt stale TopicAsyncChecks.callA true).adopted = [] ∧
    stale.core.calls.head?.map TopicAsync.Slot.phase = some (.terminal (.text 11)) := by decide

theorem unobserved_result_cannot_merge :
    let fresh := { initial with core := (TopicAsync.receive initial.core
      TopicAsyncChecks.callA (.text 11) 10) }
    (adopt fresh TopicAsyncChecks.callA true).adopted = [] := by decide

def brokenArrival (state : State) (item : Arrival) : State :=
  { enqueue state item with core := TopicAsync.changed state.core item.topic }

theorem abrupt_arrival_breaks_frame_law :
    let call := (TopicAsyncChecks.sampledA.calls[0]).call
    TopicAsync.current (brokenArrival initial arrival).core call = false ∧
    TopicAsync.current (enqueue initial arrival).core call = true := by decide

def brokenProcessed (state : State) (key : Key) : State :=
  { state with processed := state.processed ++ [key] }

theorem receipt_without_processing_enables_premature_deletion :
    deletable (brokenProcessed noticed arrival.key) notice = true ∧
    deletable noticed notice = false := by decide

def brokenMerge (state : State) (id : TopicAsync.CallId) : State :=
  { state with adopted := state.adopted ++ [id] }

theorem unreviewed_merge_and_duplicate_merge_are_detectable :
    (brokenMerge (brokenMerge results TopicAsyncChecks.callA) TopicAsyncChecks.callA).adopted =
      [TopicAsyncChecks.callA, TopicAsyncChecks.callA] ∧
    (adopt results TopicAsyncChecks.callA false).adopted = [] := by decide

end CooperativeInputChecks
