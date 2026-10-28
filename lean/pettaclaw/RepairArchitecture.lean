import AsyncWait
import RequestLifecycle

/-!
# Regression contracts for delivery, work, notices and provider lifetimes

These executable decisions mirror the housekeeping host boundary. The earlier
`RequestLifecycle` is a coarse delivery model; it does not model promotion,
checker restrictions or goal dispositions. Here those guards are explicit.

The conformance adapter compares these functions with actual SQLite host
transitions and the extracted MeTTa turn guard. That is finite checked
correspondence, not a proof of the Python interpreter, C transport, SQLite,
filesystem durability, a provider's completion, or every possible host trace.
No finite message bound proves that arbitrary tasks finish. Conditional queue
draining is inherited from `RequestLifecycle.successful_heads_eventually_drain`.
-/
namespace RepairArchitecture

open RequestLifecycle (Kind Status Boundary)

structure Request where
  id : Nat
  content : Nat
  kind : Kind
  status : Status := .active
  inputIdentity : Bool := false
  operatorChecker : Bool := true
  processed : Bool := false
deriving Repr, DecidableEq

def deliveryKind (kind : Kind) : Bool := kind == .message || kind == .notification

/-- The MeTTa turn guard, before the call to the host's processing operation. -/
def turnGate (b : Boundary) (hasActivity : Bool) : Bool :=
  RequestLifecycle.complete b && hasActivity

def process (r : Request) : Request × Bool :=
  if (deliveryKind r.kind || r.inputIdentity) && !r.processed then
    ({ r with processed := true,
              status := if deliveryKind r.kind && r.status == .active then .processed else r.status }, true)
  else (r, false)

inductive Choice where
  | keep | waitingUser | defer | addressed | reopen
deriving Repr, DecidableEq

def choiceStatus : Choice → Status
  | .keep | .reopen => .active
  | .waitingUser => .waitingUser
  | .defer => .deferred
  | .addressed => .addressed

def canDispose (r : Request) (d : Choice) : Bool :=
  !(r.status == .achieved || r.status == .cancelled) &&
  !(r.kind == .goal || r.kind == .autonomous) &&
  (d != .addressed || (r.operatorChecker && (!deliveryKind r.kind || r.processed)))

def dispose (r : Request) (d : Choice) : Request × Bool :=
  if canDispose r d then
    ({ r with status := choiceStatus d, kind := if d == .keep then .task else r.kind }, true)
  else (r, false)

theorem failed_turn_cannot_process (b : Boundary) (hasActivity : Bool)
    (failed : RequestLifecycle.complete b = false) : turnGate b hasActivity = false := by
  simp [turnGate, failed]

theorem no_activity_cannot_process (b : Boundary) : turnGate b false = false := by
  simp [turnGate]

theorem processing_preserves_record (r : Request) :
    (process r).1.id = r.id ∧ (process r).1.content = r.content ∧
    (process r).1.kind = r.kind ∧ (process r).1.operatorChecker = r.operatorChecker := by
  unfold process; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem already_processed_is_idempotent (r : Request) (done : r.processed = true) :
    process r = (r, false) := by simp [process, done]

theorem processing_cannot_claim_achievement (r : Request)
    (unfinished : r.status ≠ .achieved) : (process r).1.status ≠ .achieved := by
  unfold process
  split
  · simp only
    split <;> simp_all
  · exact unfinished

theorem processing_promoted_task_preserves_work (r : Request) (task : r.kind = .task) :
    (process r).1.status = r.status := by simp [process, deliveryKind, task]; split <;> rfl

theorem disposition_preserves_evidence (r : Request) (d : Choice) :
    (dispose r d).1.id = r.id ∧ (dispose r d).1.content = r.content ∧
    (dispose r d).1.processed = r.processed ∧
    (dispose r d).1.operatorChecker = r.operatorChecker := by
  unfold dispose; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem goal_disposition_is_rejected (r : Request) (d : Choice) (goal : r.kind = .goal) :
    dispose r d = (r, false) := by simp [dispose, canDispose, goal]

theorem autonomous_disposition_is_rejected (r : Request) (d : Choice)
    (autonomous : r.kind = .autonomous) : dispose r d = (r, false) := by
  simp [dispose, canDispose, autonomous]

theorem closed_record_cannot_reopen (r : Request) (d : Choice)
    (closed : r.status = .achieved ∨ r.status = .cancelled) : dispose r d = (r, false) := by
  rcases closed with h | h <;> simp [dispose, canDispose, h]

theorem configured_checker_cannot_be_bypassed (r : Request) (checker : r.operatorChecker = false) :
    dispose r .addressed = (r, false) := by simp [dispose, canDispose, checker]

theorem unprocessed_message_cannot_be_addressed (r : Request)
    (message : deliveryKind r.kind = true) (pending : r.processed = false) :
    dispose r .addressed = (r, false) := by simp [dispose, canDispose, message, pending]

theorem workflow_never_manufactures_achievement (r : Request) (d : Choice)
    (unfinished : r.status ≠ .achieved) : (dispose r d).1.status ≠ .achieved := by
  unfold dispose
  split
  · cases d <;> simp [choiceStatus]
  · exact unfinished

/-- The old delivery path recorded history/acknowledgement without changing the
work ledger. This is its projection onto a particular accepted record. -/
def legacySuccessfulTurns : Nat → Request → Request
  | 0, r => r
  | n + 1, r => legacySuccessfulTurns n r

theorem legacy_success_never_drains_delivery (n : Nat) (r : Request) :
    legacySuccessfulTurns n r = r := by induction n <;> simp_all [legacySuccessfulTurns]

theorem legacy_safety_allows_permanent_backlog (n : Nat) :
    (legacySuccessfulTurns n { id := 1, content := 2, kind := .message }).status = .active ∧
    (legacySuccessfulTurns n { id := 1, content := 2, kind := .message }).processed = false := by
  simp [legacy_success_never_drains_delivery]

/-- This is one successful delivery, not completion of the requested task. -/
theorem successful_message_leaves_active_backlog (r : Request)
    (message : r.kind = .message) (active : r.status = .active) (pending : r.processed = false) :
    (process r).1.status = .processed ∧ (process r).1.processed = true := by
  simp [process, deliveryKind, message, active, pending]

def activeView (rows : List Request) : List Request :=
  (rows.filter (fun r => r.status == .active)).take 8

theorem active_view_has_at_most_eight (rows : List Request) :
    (activeView rows).length ≤ 8 := List.length_take_le _ _

/-- Bounds apply to content excerpts and item counts, not arbitrary ID/checker
strings, the entire JSON encoding, token count, or all parts of a prompt. -/
def excerpt (content : List α) (limit : Nat) : List α := content.take limit

theorem excerpt_is_bounded (content : List α) (limit : Nat) :
    (excerpt content limit).length ≤ limit := List.length_take_le _ _

theorem excerpt_does_not_destroy_source (content : List α) (limit : Nat) :
    excerpt content limit ++ content.drop limit = content := List.take_append_drop _ _

def legacyView (rows : List Request) : List Request := rows.filter (fun r => r.status == .active)

theorem legacy_view_has_no_item_bound (limit : Nat) :
    ∃ rows, (rows.map fun r => r.id).Nodup ∧ (legacyView rows).length > limit := by
  let rows : List Request := (List.range (limit + 1)).map fun id =>
    { id := id, content := 2, kind := .message }
  refine ⟨rows, ?_, ?_⟩
  · simpa [rows, List.map_map, Function.comp_def] using (List.nodup_range (n := limit + 1))
  · have filtered : (List.range (limit + 1)).filter (fun _ => true) = List.range (limit + 1) :=
      List.filter_eq_self.mpr (by intro _ _; rfl)
    simp [rows, legacyView, List.filter_map, Function.comp_def, filtered]

def cachedPrefix (stable dynamic : List α) : List α := (stable ++ dynamic).take stable.length

theorem stable_first_keeps_the_prefix (stable dynamic : List α) : cachedPrefix stable dynamic = stable := by
  induction stable with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

theorem changing_context_preserves_cache_prefix (stable first second : List α) :
    cachedPrefix stable first = cachedPrefix stable second := by
  rw [stable_first_keeps_the_prefix, stable_first_keeps_the_prefix]

/-- The wire-prefix theorem concerns reuse eligibility, not provider caching,
cost, the identity of a tokenizer or a bound on prompt size. -/
def cachePacket (stable : List (List Nat)) (dynamic : List Nat) : List Nat × List Nat :=
  (stable.flatten, dynamic)

inductive RequestEvent where
  | process | dispose (choice : Choice) | neutral
deriving Repr, DecidableEq

def requestStep (r : Request) : RequestEvent → Request
  | .process => (process r).1
  | .dispose d => (dispose r d).1
  | .neutral => r

def requestRun (r : Request) (events : List RequestEvent) : Request := events.foldl requestStep r

theorem request_step_preserves_source (r : Request) (e : RequestEvent) :
    (requestStep r e).id = r.id ∧ (requestStep r e).content = r.content := by
  cases e with
  | process => exact ⟨(processing_preserves_record r).1, (processing_preserves_record r).2.1⟩
  | dispose d => exact ⟨(disposition_preserves_evidence r d).1, (disposition_preserves_evidence r d).2.1⟩
  | neutral => exact ⟨rfl, rfl⟩

theorem arbitrary_workflow_trace_preserves_source (r : Request) (events : List RequestEvent) :
    (requestRun r events).id = r.id ∧ (requestRun r events).content = r.content := by
  induction events generalizing r with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
      have first := request_step_preserves_source r e
      have rest := ih (requestStep r e)
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

theorem arbitrary_workflow_trace_cannot_claim_achievement (r : Request) (events : List RequestEvent)
    (unfinished : r.status ≠ .achieved) : (requestRun r events).status ≠ .achieved := by
  induction events generalizing r with
  | nil => exact unfinished
  | cons e es ih =>
      apply ih
      cases e with
      | process => exact processing_cannot_claim_achievement r unfinished
      | dispose d => exact workflow_never_manufactures_achievement r d unfinished
      | neutral => exact unfinished

/-- A malformed foreign value must not be salvaged by extracting digit-like
substrings. Validation covers the entire CSV before any ID is acknowledged. -/
def parseUpdateId (text : List Nat) : Option Nat := do
  if text.isEmpty || text.length > 19 ||
      !(text.all fun c => decide (48 ≤ c ∧ c ≤ 57)) ||
      (text.head? == some 48 && text.length > 1) then none
  else
    let n := text.foldl (fun n c => 10 * n + (c - 48)) 0
    if n < 2 ^ 63 then some n else none

/-- Unicode code points supplied by the adapter; keeping the parser over
lists makes its concrete checks reducible by the kernel without native axioms. -/
def splitFields : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs =>
      if c == 44 then [] :: splitFields cs
      else match splitFields cs with
        | [] => [[c]]
        | first :: rest => (c :: first) :: rest

def csvIds (text : List Nat) : Option (List Nat) := do
  if text.isEmpty then some []
  else
    let parts := splitFields text
    if parts.length > 256 then none
    else return (← parts.mapM parseUpdateId).eraseDups

theorem legacy_error_text_is_not_an_id_batch :
    csvIds [91,39,55,39,44,32,39,49,49,39,93] = none := by decide

theorem partial_invalid_csv_is_rejected_whole : csvIds [49,44,44,50] = none := by decide

theorem correct_join_keeps_exact_ids :
    csvIds [55,44,49,49] = some [7,11] := by decide

inductive NoticeState where
  | registered | submitted | deleted | expired
deriving Repr, DecidableEq

structure Notice where
  update : Nat
  sendKey : Nat
  ownedDeleteKey : Nat
  deleteKey : Option Nat := none
  message : Option Int := none
  processed : Bool := false
  state : NoticeState := .submitted
deriving Repr, DecidableEq

structure Receipt where
  key : Nat
  envelopeValid : Bool
  deliveredInteger : Bool
  message : Int
deriving Repr, DecidableEq

/-- Failed/uncertain evidence for a known key is consumed, but cannot authorize
deletion. A confirmed send receipt binds one particular positive message ID. -/
def receipt (n : Notice) (r : Receipt) : Notice × Bool :=
  if !r.envelopeValid || !(r.key == n.sendKey || n.deleteKey == some r.key) then (n, false)
  else if !r.deliveredInteger then (n, true)
  else if r.key == n.sendKey && r.message > 0 then
    if n.message.isSome && n.message != some r.message then (n, false)
    else ({ n with message := some r.message }, true)
  else if n.deleteKey == some r.key && n.processed &&
      (r.message == 0 || n.message == some r.message) then
    ({ n with state := .deleted }, true)
  else (n, false)

def acknowledgeNotice (n : Notice) (ids : List Nat) (durable : Bool) : Notice :=
  if durable && ids.contains n.update then { n with processed := true } else n

def acknowledgeCSV (n : Notice) (text : List Nat) (durable : Bool) : Notice :=
  match csvIds text with
  | none => n
  | some ids => acknowledgeNotice n ids durable

theorem malformed_ids_cannot_process_notice (n : Notice) (text : List Nat) (durable : Bool)
    (malformed : csvIds text = none) : acknowledgeCSV n text durable = n := by
  simp [acknowledgeCSV, malformed]

def pump (n : Notice) (expired : Bool) : Notice × Option Int :=
  if n.state == .registered || n.state == .submitted then
    if expired then ({ n with state := .expired }, none)
    else if n.message.isNone || !n.processed then (n, none)
    else ({ n with deleteKey := some n.ownedDeleteKey }, n.message)
  else (n, none)

theorem failed_handover_preserves_notice (n : Notice) (ids : List Nat) :
    acknowledgeNotice n ids false = n := by simp [acknowledgeNotice]

theorem foreign_input_cannot_process_notice (n : Notice) (ids : List Nat)
    (foreign : ids.contains n.update = false) (durable : Bool) :
    acknowledgeNotice n ids durable = n := by
  have notIn : n.update ∉ ids := by simpa using foreign
  simp [acknowledgeNotice, notIn]

theorem acknowledgement_is_idempotent (n : Notice) (ids : List Nat) (durable : Bool) :
    acknowledgeNotice (acknowledgeNotice n ids durable) ids durable =
      acknowledgeNotice n ids durable := by
  by_cases h : durable = true ∧ n.update ∈ ids <;> simp [acknowledgeNotice, h]

theorem unprocessed_notice_cannot_be_deleted (n : Notice) (expired : Bool)
    (pending : n.processed = false) : (pump n expired).2 = none := by
  unfold pump; split
  · split <;> simp [pending]
  · rfl

theorem unconfirmed_message_cannot_be_deleted (n : Notice) (expired : Bool)
    (unconfirmed : n.message = none) : (pump n expired).2 = none := by
  unfold pump; split
  · split <;> simp [unconfirmed]
  · rfl

theorem expired_notice_cannot_issue_deletion (n : Notice) : (pump n true).2 = none := by
  unfold pump; split <;> rfl

theorem deletion_target_is_confirmed_message (n : Notice) (expired : Bool) (target : Int)
    (issued : (pump n expired).2 = some target) : n.message = some target := by
  unfold pump at issued
  split at issued
  · split at issued
    · contradiction
    · split at issued
      · contradiction
      · exact issued
  · contradiction

theorem malformed_envelope_preserves_notice (n : Notice) (r : Receipt)
    (malformed : r.envelopeValid = false) : receipt n r = (n, false) := by
  simp [receipt, malformed]

theorem failed_evidence_preserves_notice (n : Notice) (r : Receipt)
    (failed : r.deliveredInteger = false) : (receipt n r).1 = n := by
  unfold receipt; split
  · rfl
  · simp [failed]

theorem receipt_preserves_ownership (n : Notice) (r : Receipt) :
    (receipt n r).1.update = n.update ∧ (receipt n r).1.sendKey = n.sendKey ∧
    (receipt n r).1.ownedDeleteKey = n.ownedDeleteKey ∧
    (receipt n r).1.processed = n.processed := by
  unfold receipt
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

inductive Phase where
  | claimed | submitted | completed | late | failed | uncertain
deriving Repr, DecidableEq

structure NativeCall where
  id : Nat
  epoch : Nat
  phase : Phase := .claimed
  transport : Option Nat := none
  soft : Bool := false
  bytes : Nat := 0
  quiet : Nat := 0
  result : Option Nat := none
  reservation : Nat
deriving Repr, DecidableEq

def pending (c : NativeCall) : Bool := c.phase == .claimed || c.phase == .submitted
def canClaim (rows : List NativeCall) : Bool := !(rows.any pending)
def owned (c : NativeCall) (id epoch : Nat) : Bool := c.id == id && c.epoch == epoch

def submitted (c : NativeCall) (id epoch transport : Nat) : NativeCall :=
  if owned c id epoch && c.phase == .claimed then { c with phase := .submitted, transport := some transport }
  else c

def progress (c : NativeCall) (id epoch bytes quiet : Nat) (soft : Bool) : NativeCall :=
  if owned c id epoch && c.phase == .submitted then { c with bytes := bytes, quiet := quiet, soft := soft }
  else c

def settle (c : NativeCall) (id epoch : Nat) (phase : Phase) (result : Option Nat) : NativeCall × Bool :=
  if owned c id epoch && pending c &&
      (phase == .completed || phase == .late || phase == .failed) then
    ({ c with phase := phase, result := result }, true)
  else (c, false)

def recover (c : NativeCall) (processAlive : Bool) : NativeCall :=
  if pending c && !processAlive then { c with phase := .uncertain } else c

theorem progress_preserves_pending (c : NativeCall) (id epoch bytes quiet : Nat) (soft : Bool) :
    pending (progress c id epoch bytes quiet soft) = pending c := by
  unfold progress; split <;> rfl

theorem soft_wait_cannot_open_second_slot (c : NativeCall) (id epoch bytes quiet : Nat)
    (live : pending c = true) : canClaim [progress c id epoch bytes quiet true] = false := by
  simp [canClaim, progress_preserves_pending, live]

theorem progress_does_not_complete (c : NativeCall) (id epoch bytes quiet : Nat) (soft : Bool) :
    (progress c id epoch bytes quiet soft).phase = c.phase ∧
    (progress c id epoch bytes quiet soft).result = c.result ∧
    (progress c id epoch bytes quiet soft).reservation = c.reservation := by
  unfold progress; split <;> exact ⟨rfl, rfl, rfl⟩

theorem foreign_epoch_cannot_settle (c : NativeCall) (id epoch : Nat) (p : Phase)
    (result : Option Nat) (foreign : c.epoch ≠ epoch) : settle c id epoch p result = (c, false) := by
  simp [settle, owned, foreign]

theorem terminal_cannot_be_overwritten (c : NativeCall) (id epoch : Nat) (p : Phase)
    (result : Option Nat) (terminal : pending c = false) : settle c id epoch p result = (c, false) := by
  simp [settle, terminal]

theorem settlement_preserves_reservation (c : NativeCall) (id epoch : Nat) (p : Phase)
    (result : Option Nat) : (settle c id epoch p result).1.reservation = c.reservation := by
  unfold settle; split <;> rfl

theorem dead_process_retains_uncertainty_and_reservation (c : NativeCall)
    (live : pending c = true) : (recover c false).phase = .uncertain ∧
      (recover c false).reservation = c.reservation ∧ (recover c false).id = c.id := by
  simp [recover, live]

inductive NativeEvent where
  | submit (id epoch transport : Nat)
  | progress (id epoch bytes quiet : Nat) (soft : Bool)
  | settle (id epoch : Nat) (phase : Phase) (result : Option Nat)
  | recover (processAlive : Bool)
deriving Repr, DecidableEq

def nativeStep (c : NativeCall) : NativeEvent → NativeCall
  | .submit id epoch handle => submitted c id epoch handle
  | .progress id epoch bytes quiet soft => progress c id epoch bytes quiet soft
  | .settle id epoch phase result => (settle c id epoch phase result).1
  | .recover alive => recover c alive

def nativeRun (c : NativeCall) (events : List NativeEvent) : NativeCall := events.foldl nativeStep c

theorem native_step_preserves_owner_and_reservation (c : NativeCall) (e : NativeEvent) :
    (nativeStep c e).id = c.id ∧ (nativeStep c e).epoch = c.epoch ∧
    (nativeStep c e).reservation = c.reservation := by
  cases e <;> simp only [nativeStep, submitted, progress, settle, recover] <;> split <;> simp_all

theorem arbitrary_native_trace_preserves_owner_and_reservation (c : NativeCall) (events : List NativeEvent) :
    (nativeRun c events).id = c.id ∧ (nativeRun c events).epoch = c.epoch ∧
    (nativeRun c events).reservation = c.reservation := by
  induction events generalizing c with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e es ih =>
      have first := native_step_preserves_owner_and_reservation c e
      have rest := ih (nativeStep c e)
      exact ⟨rest.1.trans first.1, rest.2.1.trans first.2.1, rest.2.2.trans first.2.2⟩

/-- The old foreground deadline was also a destructive transport deadline. -/
def legacyTimeout (c : AsyncWait.Call) : AsyncWait.Call :=
  AsyncWait.settle c c.id .transportFailure

theorem legacy_timeout_rejects_late_answer (c : AsyncWait.Call) (value : Nat)
    (live : c.terminal = none) :
    (AsyncWait.settle (legacyTimeout c) c.id (.answer value)).terminal = some .transportFailure := by
  simp [legacyTimeout, AsyncWait.settle, live]

theorem soft_timeout_accepts_late_answer (c : AsyncWait.Call) (value : Nat)
    (live : c.terminal = none) :
    (AsyncWait.settle (AsyncWait.softWait c) c.id (.answer value)).terminal = some (.answer value) :=
  AsyncWait.completion_after_soft_wait c value live

end RepairArchitecture
