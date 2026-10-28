import RepairArchitecture

/-!
# Routed notice cleanup and conditional progress

A visible answer, durable input settlement, deletion intent and confirmed
deletion are different events. Route and ownership are captured with a notice;
changing the currently selected chat cannot redirect its cleanup.

These contracts compose the executable `RepairArchitecture` transitions.
Progress requires a successful durable input boundary, service of this notice,
and a confirming transport receipt before expiry. There is no assumption that
arbitrary providers, tasks or Telegram requests always succeed. Expiry closes
local tracking without claiming that the remote message was deleted.
-/
namespace NoticeProtocol

open RepairArchitecture
open RequestLifecycle (Boundary)

structure Route where
  chat : Int
  thread : Nat
deriving Repr, DecidableEq

structure OwnedNotice where
  route : Route
  notice : Notice
deriving Repr, DecidableEq

structure DeleteIntent where
  route : Route
  key : Nat
  message : Int
deriving Repr, DecidableEq

/-- Visible delivery is evidence about the answer, not the input commit. -/
def visibleReply (n : OwnedNotice) : OwnedNotice := n

def settleInput (n : OwnedNotice) (ids : List Nat) (b : Boundary) : OwnedNotice :=
  { n with notice := acknowledgeNotice n.notice ids (RequestLifecycle.complete b) }

def issue (n : OwnedNotice) (expired : Bool) : OwnedNotice × Option DeleteIntent :=
  let next := pump n.notice expired
  ({ n with notice := next.1 },
    next.2.map fun message => ⟨n.route, n.notice.ownedDeleteKey, message⟩)

def observe (n : OwnedNotice) (r : Receipt) : OwnedNotice :=
  { n with notice := (receipt n.notice r).1 }

/-- A failed/unavailable attempt retains its keyed intent for retry. An accepted
attempt includes a correlated confirming receipt; submission alone is not this
receipt. Zero is the channel protocol's confirmed deletion result. -/
def attempt (n : OwnedNotice) (confirmed : Bool) : OwnedNotice :=
  let sent := issue n false
  match sent.2 with
  | none => sent.1
  | some intent =>
    if confirmed then observe sent.1 ⟨intent.key, true, true, 0⟩ else sent.1

def ready (n : OwnedNotice) : Prop :=
  n.notice.processed = true ∧ n.notice.message.isSome = true ∧
    (n.notice.state = .registered ∨ n.notice.state = .submitted)

def failedAttempts (n : OwnedNotice) : Nat → OwnedNotice
  | 0 => n
  | k + 1 => failedAttempts (attempt n false) k

inductive Event where
  | visible
  | settled (ids : List Nat) (boundary : Boundary)
  | tick (expired : Bool)
  | delivery (evidence : Receipt)
deriving Repr, DecidableEq

def step (n : OwnedNotice) : Event → OwnedNotice
  | .visible => visibleReply n
  | .settled ids b => settleInput n ids b
  | .tick expired => (issue n expired).1
  | .delivery r => observe n r

def run (n : OwnedNotice) : List Event → OwnedNotice
  | [] => n
  | e :: rest => run (step n e) rest

theorem visible_answer_preserves_pending_input (n : OwnedNotice) :
    visibleReply n = n := rfl

theorem reply_does_not_authorize_deletion (n : OwnedNotice)
    (pending : n.notice.processed = false) : (issue (visibleReply n) false).2 = none := by
  simp [visibleReply, issue, unprocessed_notice_cannot_be_deleted n.notice false pending]

theorem incomplete_input_commit_stutters (n : OwnedNotice) (ids : List Nat) (b : Boundary)
    (failed : RequestLifecycle.complete b = false) : settleInput n ids b = n := by
  simp [settleInput, failed, acknowledgeNotice]

theorem another_input_commit_stutters (n : OwnedNotice) (ids : List Nat) (b : Boundary)
    (other : ids.contains n.notice.update = false) : settleInput n ids b = n := by
  simp [settleInput, foreign_input_cannot_process_notice n.notice ids other]

theorem commit_preserves_route (n : OwnedNotice) (ids : List Nat) (b : Boundary) :
    (settleInput n ids b).route = n.route := rfl

theorem issue_preserves_route (n : OwnedNotice) (expired : Bool) :
    (issue n expired).1.route = n.route := rfl

theorem intent_uses_captured_route (n : OwnedNotice) (expired : Bool) (intent : DeleteIntent)
    (sent : (issue n expired).2 = some intent) : intent.route = n.route := by
  unfold issue at sent
  cases h : (pump n.notice expired).2 with
  | none => simp [h] at sent
  | some message => simp [h] at sent; subst intent; rfl

theorem intent_uses_owned_key (n : OwnedNotice) (expired : Bool) (intent : DeleteIntent)
    (sent : (issue n expired).2 = some intent) : intent.key = n.notice.ownedDeleteKey := by
  unfold issue at sent
  cases h : (pump n.notice expired).2 with
  | none => simp [h] at sent
  | some message => simp [h] at sent; subst intent; rfl

theorem intent_uses_confirmed_message (n : OwnedNotice) (expired : Bool) (intent : DeleteIntent)
    (sent : (issue n expired).2 = some intent) : n.notice.message = some intent.message := by
  unfold issue at sent
  cases h : (pump n.notice expired).2 with
  | none => simp [h] at sent
  | some message =>
    simp [h] at sent; subst intent
    exact deletion_target_is_confirmed_message n.notice expired message h

theorem failed_delivery_cannot_change_notice (n : OwnedNotice) (r : Receipt)
    (failed : r.deliveredInteger = false) : observe n r = n := by
  simp [observe, failed_evidence_preserves_notice n.notice r failed]

theorem owned_route_survives_every_event (n : OwnedNotice) (e : Event) :
    (step n e).route = n.route := by cases e <;> rfl

theorem owned_route_survives_every_trace (events : List Event) (n : OwnedNotice) :
    (run n events).route = n.route := by
  induction events generalizing n with
  | nil => rfl
  | cons e rest ih => simp [run, ih, owned_route_survives_every_event]

theorem ready_commit_issues_intent (n : OwnedNotice) (ids : List Nat) (b : Boundary)
    (done : RequestLifecycle.complete b = true) (included : ids.contains n.notice.update = true)
    (known : n.notice.message.isSome = true)
    (live : n.notice.state = .registered ∨ n.notice.state = .submitted) :
    ((issue (settleInput n ids b) false).2).isSome = true := by
  have hin : n.notice.update ∈ ids := by simpa using included
  cases message : n.notice.message with
  | none => simp [message] at known
  | some m =>
    rcases live with h | h <;>
      simp [issue, settleInput, acknowledgeNotice, done, hin, pump, h, message]

theorem ready_attempt_confirms_deletion (n : OwnedNotice) (h : ready n) :
    (attempt n true).notice.state = .deleted := by
  rcases h with ⟨processed, known, live⟩
  cases message : n.notice.message with
  | none => simp [message] at known
  | some m =>
    rcases live with state | state <;>
      simp [attempt, issue, pump, state, message, processed, observe, receipt]

theorem failed_attempt_preserves_readiness (n : OwnedNotice) (h : ready n) :
    ready (attempt n false) := by
  rcases h with ⟨processed, known, live⟩
  cases message : n.notice.message with
  | none => simp [message] at known
  | some m =>
    rcases live with state | state <;>
      simp [attempt, issue, pump, state, message, processed, ready]

theorem failed_attempt_keeps_key_and_target (n : OwnedNotice) (h : ready n) :
    issue (attempt n false) false = issue n false := by
  rcases h with ⟨processed, known, live⟩
  cases message : n.notice.message with
  | none => simp [message] at known
  | some m =>
    rcases live with state | state <;>
      simp [attempt, issue, pump, state, message, processed]

theorem finite_failures_preserve_readiness (k : Nat) (n : OwnedNotice) (h : ready n) :
    ready (failedAttempts n k) := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => exact ih (attempt n false) (failed_attempt_preserves_readiness n h)

/-- Any finite number of unavailable/failed attempts can precede success.
Fair scheduling and a confirming response before expiry supply the finite k;
the theorem does not assert those environmental conditions unconditionally. -/
theorem finite_retries_then_confirmation_delete (k : Nat) (n : OwnedNotice) (h : ready n) :
    (attempt (failedAttempts n k) true).notice.state = .deleted :=
  ready_attempt_confirms_deletion _ (finite_failures_preserve_readiness k n h)

theorem confirmed_deletion_is_absorbing (n : OwnedNotice) (confirmed : Bool)
    (deleted : n.notice.state = .deleted) : attempt n confirmed = n := by
  simp [attempt, issue, pump, deleted]

theorem expiry_terminates_local_tracking (n : OwnedNotice) :
    (issue n true).1.notice.state = .deleted ∨ (issue n true).1.notice.state = .expired := by
  cases h : n.notice.state <;> simp [issue, pump, h]

theorem expiry_issues_no_remote_deletion (n : OwnedNotice) :
    (issue n true).2 = none := by
  simp [issue, expired_notice_cannot_issue_deletion]

theorem visible_reply_is_not_input_settlement_counterexample :
    let n : OwnedNotice := ⟨⟨-42, 0⟩, { update := 7, sendKey := 1, ownedDeleteKey := 2, message := some 501 }⟩
    (issue (visibleReply n) false).2 = none ∧
    ((issue (settleInput n [7] ⟨true, true, true⟩) false).2).isSome = true := by decide

end NoticeProtocol
