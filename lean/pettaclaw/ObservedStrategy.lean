import ConversationContinuation
import CodingAgent
import OmegaArchitecture
import ContextProjection
import FeedbackSensitiveBatch
import AdmissionFrontier

/-!
# An observed, interruptible strategy over the shared request ledger

The managed host composes existing source models rather than changing their
reference loops. Iter supplies ordered failure-transactional preparation and
checkpoint laws; Codex supplies captured routing authority and correlated
action feedback; Omega supplies explicit wake scheduling. Request commitments
remain in `ConversationContinuation`, outside all replaceable preparations.

A provider request captures the mode, causal revision, tool router and focused
obligation together. New input, router replacement, restart and mode selection
advance the revision. A reply to an older snapshot can be recorded as stale but
cannot initiate an effect. Already issued effects remain pending across these
events: interruption is not rollback, and restart is not permission to replay.

Provider admission and dependent-effect admission are separate. Unknown broker
outcomes cannot freeze thinking; they retain their observation barrier for
new effects. This strategic quotient conservatively treats every command as
an effect. AdmissionFrontier supplies the richer observation/effect contract;
TopicAsync reuses this strategic gate for its bounded owned call pool. Strict
upstream profiles keep their own loops.

Host assumptions include the previous request-ledger assumptions, a durable
atomic checkpoint, faithful provider and broker correlation, monotone clock
observations, and trusted search-scope/coverage validation. Transformations
are pure functions at this model boundary; arbitrary Python side effects are
not certified. Request allowance and cooldown are configurable host policy.
No theorem asserts that model prose is true or that arbitrary tasks terminate.
-/

namespace ObservedStrategy

open Mettapedia.CognitiveArchitecture.Agent

inductive Mode where
  | coding | iter | omega | combined
deriving Repr, DecidableEq

structure Snapshot where
  serial : Nat
  revision : Nat
  mode : Mode
  focus : ConversationContinuation.RequestKey
  obligation : ConversationContinuation.Status
  boundary : IterArchitecture.Boundary
  router : CodingAgent.RequestView
deriving Repr, DecidableEq

structure Dispatch where
  ticket : ConversationContinuation.Ticket
  tool : Nat
  snapshot : Snapshot
deriving Repr, DecidableEq

inductive DecisionRecord where
  | stale (serial : Nat)
  | failed (serial error : Nat)
  | text (serial answer : Nat)
  | denied (serial tool : Nat)
  | proposed (dispatch : Dispatch)
deriving Repr, DecidableEq

structure State where
  requests : ConversationContinuation.State
  boundary : IterArchitecture.Boundary
  router : CodingAgent.RequestView
  mode : Mode
  revision : Nat
  nextSample : Nat
  allowance : Nat
  cooldownUntil : Int
  pending : Option Snapshot
  dispatch : Option Dispatch
  decisions : List DecisionRecord
  omega : OmegaArchitecture.State
  wakePolicy : OmegaArchitecture.Config

def initial (allowance : Nat) (wakePolicy : OmegaArchitecture.Config := {}) : State :=
  ⟨ConversationContinuation.initial, ⟨[], []⟩, ⟨[], [], []⟩, .combined, 0, 0, allowance, 0,
    none, none, [], OmegaArchitecture.boot wakePolicy [], wakePolicy⟩

def deliver (state : State) (key : ConversationContinuation.RequestKey) : State :=
  if key ∈ state.requests.accepted then state
  else
    { state with
      requests := ConversationContinuation.accept state.requests key
      revision := state.revision + 1 }

def acknowledge (state : State) (key : ConversationContinuation.RequestKey) : State :=
  { state with requests := ConversationContinuation.acknowledge state.requests key }

def pause (state : State) : State :=
  { state with
    requests := ConversationContinuation.interrupt state.requests
    revision := state.revision + 1 }

def resume (state : State) : State :=
  { state with requests := ConversationContinuation.resume state.requests }

def selectMode (state : State) (mode : Mode) : State :=
  { state with mode := mode, revision := state.revision + 1 }

def replaceRouter (state : State) (router : CodingAgent.RequestView) : State :=
  { state with router := router, revision := state.revision + 1 }

def compact (state : State) (budget : Nat) : State :=
  { state with
    requests := ConversationContinuation.compact state.requests
      (fun log => log.drop (log.length - budget)) }

/-- The mutable boundary cannot expose a pending obligation only through a
lossy message list: it has a separate protected field in the snapshot. -/
def snapshot (state : State) (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) : Snapshot :=
  let (prepared, router) := CodingAgent.prepareWithIter changes
    state.boundary.messages { state.router with advertised := state.boundary.advertised }
  ⟨state.nextSample, state.revision, state.mode, focus,
    state.requests.commitments focus, prepared, router⟩

/-- Runnable thought depends on input/control and the owned provider slot,
not on the broker's pending or unobserved action. -/
def ready (state : State) : Bool :=
  !state.requests.interrupted && state.requests.inbox.isEmpty &&
  decide (state.pending = none)

/-- The signed host clock is projected by its due predicate. The abstract
clock coordinates encode that predicate, not elapsed wall time. -/
def admissionControls (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) : AdmissionFrontier.Controls :=
  { available := state.requests.inbox.isEmpty &&
      decide (state.requests.commitments focus = .active)
    paused := state.requests.interrupted
    pending := state.pending.map Snapshot.serial
    allowance := some state.allowance
    cooldown := if state.cooldownUntil ≤ now then 0 else 1 }

def canCapture (state : State) (now : Int) (focus : ConversationContinuation.RequestKey) : Bool :=
  decide (AdmissionFrontier.thoughtDenial (admissionControls state now focus) = none)

theorem canCapture_eq (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) :
    canCapture state now focus =
      (ready state && decide (state.requests.commitments focus = .active) &&
        decide (0 < state.allowance) && decide (state.cooldownUntil ≤ now)) := by
  cases pending : state.pending <;>
    cases interrupted : state.requests.interrupted <;>
    by_cases inbox : state.requests.inbox.isEmpty = true <;>
    by_cases active : state.requests.commitments focus = .active <;>
    by_cases allowance : state.allowance = 0 <;>
    by_cases due : state.cooldownUntil ≤ now <;>
    simp_all [canCapture, admissionControls, AdmissionFrontier.thoughtDenial, ready] <;> omega

/-- Outcome uncertainty still gates every command in this conservative
strategic quotient. The typed observation contract lives in AdmissionFrontier. -/
def effectsReady (state : State) : Bool :=
  decide (state.requests.phase = .ready) && decide (state.dispatch = none)

/-- Completion requires both an available provider coordinate and a settled
effect frontier. Runnable thought alone cannot certify task completion. -/
def completionReady (state : State) : Bool := ready state && effectsReady state

/-- Every provider attempt spends one allowance, including a failed attempt.
There is no hidden retry transition inside this submission. -/
def capture (state : State) (now : Int) (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) : State :=
  if canCapture state now focus then
    { state with
      pending := some (snapshot state focus changes)
      nextSample := state.nextSample + 1, allowance := state.allowance - 1
      omega := OmegaArchitecture.armWake state.wakePolicy state.omega now }
  else state

def current (state : State) (snap : Snapshot) : Bool :=
  decide (snap.revision = state.revision) && decide (snap.mode = state.mode) &&
  !state.requests.interrupted && state.requests.inbox.isEmpty

/-- Advertising a schema grants neither an implementation nor permission. -/
def admitCommand (snap : Snapshot) (ticket : ConversationContinuation.Ticket) (tool : Nat) :
    Option Dispatch :=
  if ticket.request = snap.focus ∧ tool ∈ snap.router.executable ∧
      tool ∈ snap.router.permitted then some ⟨ticket, tool, snap⟩ else none

def admitEffect (state : State) (snap : Snapshot)
    (ticket : ConversationContinuation.Ticket) (tool : Nat) : Option Dispatch :=
  if effectsReady state then admitCommand snap ticket tool else none

inductive Reply where
  | failure (error : Nat) (retryAfter : Int)
  | text (answer : Nat)
  | command (ticket : ConversationContinuation.Ticket) (tool : Nat)
deriving Repr, DecidableEq

def handleReply (state : State) (now : Int) (snap : Snapshot) : Reply → State
  | .failure error retryAfter =>
      { state with
        pending := none
        cooldownUntil := max state.cooldownUntil (now + max 1 retryAfter),
        decisions := state.decisions ++ [.failed snap.serial error] }
  | .text answer =>
      { state with
        pending := none
        decisions := state.decisions ++ [.text snap.serial answer] }
  | .command ticket tool =>
      match admitEffect state snap ticket tool with
      | none =>
          { state with
            pending := none
            decisions := state.decisions ++ [.denied snap.serial tool] }
      | some dispatch =>
          let proposed := ConversationContinuation.propose state.requests ticket
          if proposed.phase = .awaitingBroker ticket then
            { state with
              requests := proposed, pending := none
              dispatch := some dispatch,
              decisions := state.decisions ++ [.proposed dispatch] }
          else
            { state with
              pending := none
              decisions := state.decisions ++ [.denied snap.serial tool] }

def reply (state : State) (now : Int) (serial : Nat) (response : Reply) : State :=
  match state.pending with
  | none => state
  | some snap =>
      if serial ≠ snap.serial then state
      else if current state snap then handleReply state now snap response
      else
        { state with
          pending := none
          decisions := state.decisions ++ [.stale serial] }

def report (state : State) (receipt : ConversationContinuation.Receipt) : State :=
  match state.dispatch with
  | none => state
  | some dispatch =>
      if receipt.ticket = dispatch.ticket ∧
          state.requests.phase = .awaitingBroker receipt.ticket then
        { state with
          requests := ConversationContinuation.brokerResult state.requests receipt
          dispatch := none, revision := state.revision + 1 }
      else state

def observe (state : State) (ticket : ConversationContinuation.Ticket) : State :=
  { state with requests := ConversationContinuation.observeResult state.requests ticket }

def finish (accepts : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool) (state : State)
    (key : ConversationContinuation.RequestKey) (receipt : ConversationContinuation.Receipt) : State :=
  if state.requests.inbox.isEmpty && decide (state.pending = none) &&
      decide (state.requests.phase = .ready) then
    { state with requests := ConversationContinuation.complete accepts state.requests key receipt }
  else state

def cooldown (state : State) (deadline : Int) : State :=
  { state with cooldownUntil := max state.cooldownUntil deadline }

/-- Omega's wake policy is a scheduling coordinate, not a completion signal. -/
def omegaWake (state : State) (now : Int) : State :=
  { state with omega := OmegaArchitecture.idleWake state.wakePolicy state.omega now }

/-- `State` is the durable checkpoint boundary. Restore discards a volatile
provider request and invalidates late replies. Issued calls, results, mode,
remaining allowance and serial allocation survive unchanged. -/
def restore (checkpoint : State) : State :=
  { checkpoint with pending := none, revision := checkpoint.revision + 1 }

/-! A search result may certify absence only within its exact checked scope.
Coverage is supplied by the host validator, not inferred from an empty hit list. -/

structure SearchReport where
  scope : Nat
  revision : Nat
  hits : List Nat
  finished : Bool
  completeCoverage : Bool
deriving Repr, DecidableEq

def searchObservation (scope revision : Nat) (report : SearchReport) :
    ContextProjection.Observation (List Nat) :=
  if report.scope ≠ scope ∨ report.revision ≠ revision ∨ !report.finished then
    .unavailable
  else if report.hits.isEmpty then
    if report.completeCoverage then .absent else .unavailable
  else .known report.hits

/-! ## Preparation, authority and interruption laws -/

theorem preparation_is_exact_iter_fold (state : State)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    (snapshot state focus changes).boundary =
      IterArchitecture.applyTransformations changes state.boundary := rfl

theorem preparation_reuses_coding_agent_connector (state : State)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    ((snapshot state focus changes).boundary, (snapshot state focus changes).router) =
      CodingAgent.prepareWithIter changes state.boundary.messages
        { state.router with advertised := state.boundary.advertised } := rfl

theorem preparation_cannot_erase_focused_work (state : State)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    (snapshot state focus changes).obligation =
      state.requests.commitments focus := rfl

theorem transformations_do_not_grant_execution_authority (state : State)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    (snapshot state focus changes).router.executable = state.router.executable ∧
    (snapshot state focus changes).router.permitted = state.router.permitted :=
  ⟨rfl, rfl⟩

theorem failed_preparation_stutters (state : State)
    (focus : ConversationContinuation.RequestKey) :
    snapshot state focus [fun _ => none] = snapshot state focus [] := rfl

theorem mode_selection_preserves_work_and_effects (state : State) (mode : Mode) :
    (selectMode state mode).requests = state.requests ∧
    (selectMode state mode).dispatch = state.dispatch := ⟨rfl, rfl⟩

theorem interruption_preserves_pending_effect (state : State) :
    (pause state).dispatch = state.dispatch ∧
    (pause state).requests.issued = state.requests.issued ∧
    (pause state).requests.journal = state.requests.journal := ⟨rfl, rfl, rfl⟩

theorem duplicate_input_is_stutter (state : State)
    (key : ConversationContinuation.RequestKey)
    (accepted : key ∈ state.requests.accepted) : deliver state key = state := by
  simp [deliver, accepted]

theorem snapshot_revision_changes_after_fresh_input (state : State)
    (key : ConversationContinuation.RequestKey)
    (fresh : key ∉ state.requests.accepted) :
    (deliver state key).revision = state.revision + 1 := by
  simp [deliver, fresh]

theorem stale_revision_cannot_be_current (state : State) (snap : Snapshot)
    (stale : snap.revision ≠ state.revision) : current state snap = false := by
  simp [current, stale]

theorem wrong_serial_does_not_consume_pending_request (state : State)
    (snap : Snapshot) (now : Int) (serial : Nat) (response : Reply)
    (pending : state.pending = some snap) (wrong : serial ≠ snap.serial) :
    reply state now serial response = state := by
  simp [reply, pending, wrong]

theorem stale_reply_preserves_work_and_effects (state : State)
    (snap : Snapshot) (now : Int) (response : Reply)
    (pending : state.pending = some snap) (stale : snap.revision ≠ state.revision) :
    (reply state now snap.serial response).requests = state.requests ∧
    (reply state now snap.serial response).dispatch = state.dispatch := by
  simp [reply, pending, stale_revision_cannot_be_current state snap stale]

theorem mode_change_invalidates_old_snapshot (state : State) (mode : Mode)
    (snap : Snapshot) (same : snap.revision = state.revision) :
    current (selectMode state mode) snap = false := by
  have stale : snap.revision ≠ state.revision + 1 := by omega
  simp [current, selectMode, stale]

theorem admitted_command_has_captured_authority (snap : Snapshot)
    (ticket : ConversationContinuation.Ticket) (tool : Nat) (dispatch : Dispatch)
    (admitted : admitCommand snap ticket tool = some dispatch) :
    ticket.request = snap.focus ∧ tool ∈ snap.router.executable ∧
    tool ∈ snap.router.permitted ∧ dispatch.snapshot = snap ∧
    dispatch.ticket = ticket ∧ dispatch.tool = tool := by
  unfold admitCommand at admitted
  split at admitted
  · rename_i allowed
    have equal : dispatch = ⟨ticket, tool, snap⟩ := Option.some.inj admitted.symm
    subst dispatch
    exact ⟨allowed.1, allowed.2.1, allowed.2.2, rfl, rfl, rfl⟩
  · contradiction

theorem another_request_cannot_use_the_snapshot (snap : Snapshot)
    (ticket : ConversationContinuation.Ticket) (tool : Nat)
    (different : ticket.request ≠ snap.focus) :
    admitCommand snap ticket tool = none := by
  simp [admitCommand, different]

theorem advertisement_alone_cannot_authorize (snap : Snapshot)
    (ticket : ConversationContinuation.Ticket) (tool : Nat)
    (missing : tool ∉ snap.router.executable) :
    admitCommand snap ticket tool = none := by
  simp [admitCommand, missing]

/-! ## Bounded attempts and rest without false completion -/

theorem exhausted_allowance_blocks_capture (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (empty : state.allowance = 0)
    (changes : List IterArchitecture.Transformation) :
    capture state now focus changes = state := by
  simp [capture, canCapture_eq, empty]

theorem cooldown_blocks_early_capture (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (early : now < state.cooldownUntil)
    (changes : List IterArchitecture.Transformation) :
    capture state now focus changes = state := by
  have notDue : ¬state.cooldownUntil ≤ now := by omega
  simp [capture, canCapture_eq, notDue]

theorem capture_preserves_request_ledger (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    (capture state now focus changes).requests = state.requests := by
  unfold capture
  split <;> rfl

theorem capture_conserves_request_budget (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) :
    (capture state now focus changes).allowance +
        (capture state now focus changes).nextSample =
      state.allowance + state.nextSample := by
  unfold capture
  split
  · rename_i admitted
    have facts : ready state = true ∧
        state.requests.commitments focus = .active ∧
        0 < state.allowance ∧ state.cooldownUntil ≤ now := by
      simpa only [canCapture_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
        using admitted
    have enough := facts.2.2.1
    simp only
    omega
  · rfl

theorem failure_uses_positive_cooldown (state : State) (now retry : Int)
    (snap : Snapshot) (error : Nat) :
    now + 1 ≤ (handleReply state now snap (.failure error retry)).cooldownUntil := by
  simp only [handleReply]
  have bound : (1 : Int) ≤ max 1 retry := Int.le_max_left _ _
  have retained := Int.le_max_right state.cooldownUntil (now + max 1 retry)
  omega

theorem provider_failure_preserves_pending_work (state : State) (now retry : Int)
    (snap : Snapshot) (error : Nat) :
    (handleReply state now snap (.failure error retry)).requests = state.requests ∧
    (handleReply state now snap (.failure error retry)).allowance = state.allowance :=
  ⟨rfl, rfl⟩

theorem provider_text_is_not_task_fulfillment (state : State) (now : Int)
    (snap : Snapshot) (answer : Nat) :
    (handleReply state now snap (.text answer)).requests = state.requests := rfl

theorem omega_wake_is_scheduling_only (state : State) (now : Int) :
    (omegaWake state now).requests = state.requests ∧
    (omegaWake state now).allowance = state.allowance ∧
    (omegaWake state now).omega =
      OmegaArchitecture.idleWake state.wakePolicy state.omega now := ⟨rfl, rfl, rfl⟩

theorem admitted_capture_arms_omega_wake (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation)
    (admitted : canCapture state now focus = true) :
    (capture state now focus changes).omega.nextWake =
      some (now + state.wakePolicy.wakeInterval) := by
  simp [capture, admitted, OmegaArchitecture.armWake]

theorem scheduled_wake_is_strict_and_can_renew (state : State) (deadline : Int)
    (scheduled : state.omega.nextWake = some deadline) :
    (omegaWake state deadline).omega = state.omega ∧
    (omegaWake state (deadline + 1)).omega.loops = 1 + state.wakePolicy.wakeLoops :=
  OmegaArchitecture.wake_is_strict state.wakePolicy state.omega deadline scheduled

theorem rest_preserves_unfinished_work (state : State) (deadline : Int)
    (key : ConversationContinuation.RequestKey) :
    (cooldown state deadline).requests.commitments key = state.requests.commitments key := rfl

theorem restored_checkpoint_preserves_work_effects_and_budget (state : State) :
    (restore state).requests = state.requests ∧
    (restore state).dispatch = state.dispatch ∧
    (restore state).allowance = state.allowance ∧
    (restore state).nextSample = state.nextSample ∧
    (restore state).mode = state.mode ∧ (restore state).pending = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem restored_checkpoint_invalidates_previous_snapshot (state : State)
    (snap : Snapshot) (same : snap.revision = state.revision) :
    current (restore state) snap = false := by
  have stale : snap.revision ≠ state.revision + 1 := by omega
  simp [current, restore, stale]

/-! ## Evidence-aware claims -/

theorem unfinished_search_does_not_certify_absence (scope revision : Nat)
    (report : SearchReport) (unfinished : report.finished = false) :
    searchObservation scope revision report = .unavailable := by
  simp [searchObservation, unfinished]

theorem partial_empty_search_does_not_certify_absence (scope revision : Nat)
    (report : SearchReport) (empty : report.hits = [])
    (incomplete : report.completeCoverage = false) :
    searchObservation scope revision report = .unavailable := by
  simp [searchObservation, empty, incomplete]

theorem verified_absence_requires_current_complete_scope (scope revision : Nat)
    (report : SearchReport) (absent : searchObservation scope revision report = .absent) :
    report.scope = scope ∧ report.revision = revision ∧
    report.finished = true ∧ report.hits = [] ∧ report.completeCoverage = true := by
  unfold searchObservation at absent
  split at absent
  · contradiction
  · rename_i available
    have same : report.scope = scope ∧ report.revision = revision ∧
        report.finished = true := by
      simpa using available
    split at absent
    · rename_i empty
      split at absent
      · rename_i complete
        exact ⟨same.1, same.2.1, same.2.2, by simpa using empty, complete⟩
      · contradiction
    · contradiction

theorem unavailable_search_preserves_last_known (scope revision : Nat)
    (report : SearchReport) (old : Option (List Nat))
    (unavailable : searchObservation scope revision report = .unavailable) :
    ContextProjection.admit old (searchObservation scope revision report) = old := by
  rw [unavailable]
  exact ContextProjection.unavailable_preserves_last_known old

/-! ## Observation barriers and checked fulfillment -/

theorem broker_frontier_cannot_block_thinking (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (phase : ConversationContinuation.Phase)
    (dispatch : Option Dispatch) :
    canCapture { state with
      requests := { state.requests with phase := phase }
      dispatch := dispatch } now focus = canCapture state now focus := rfl

theorem awaiting_effect_blocks_new_effects (state : State)
    (ticket : ConversationContinuation.Ticket)
    (waiting : state.requests.phase = .awaitingBroker ticket) :
    effectsReady state = false := by simp [effectsReady, waiting]

theorem unobserved_result_blocks_new_effects (state : State)
    (receipt : ConversationContinuation.Receipt)
    (waiting : state.requests.phase = .awaitingObservation receipt) :
    effectsReady state = false := by simp [effectsReady, waiting]

theorem blocked_effect_preserves_broker (state : State) (now : Int) (snap : Snapshot)
    (ticket : ConversationContinuation.Ticket) (tool : Nat)
    (blocked : effectsReady state = false) :
    (handleReply state now snap (.command ticket tool)).requests = state.requests ∧
    (handleReply state now snap (.command ticket tool)).dispatch = state.dispatch := by
  simp [handleReply, admitEffect, blocked]

theorem pending_input_blocks_capture (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation)
    (pending : state.requests.inbox.isEmpty = false) :
    capture state now focus changes = state := by
  simp [capture, canCapture_eq, ready, pending]

theorem admitted_capture_submits_exactly_one_attempt (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation)
    (admitted : canCapture state now focus = true) :
    (capture state now focus changes).pending = some (snapshot state focus changes) ∧
    (capture state now focus changes).nextSample = state.nextSample + 1 ∧
    (capture state now focus changes).allowance = state.allowance - 1 := by
  simp [capture, admitted]

theorem eligible_unfinished_work_can_capture (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (available : ready state = true)
    (active : state.requests.commitments focus = .active)
    (budget : 0 < state.allowance) (due : state.cooldownUntil ≤ now) :
    canCapture state now focus = true := by
  simp [canCapture_eq, available, active, budget, due]

theorem handle_reply_consumes_provider_slot (state : State) (now : Int)
    (snap : Snapshot) (response : Reply) :
    (handleReply state now snap response).pending = none := by
  cases response with
  | failure => rfl
  | text => rfl
  | command ticket tool =>
      cases admitted : admitEffect state snap ticket tool <;> simp [handleReply, admitted]
      split <;> rfl

theorem provider_response_cannot_be_delivered_twice (state : State) (now : Int)
    (serial : Nat) (response : Reply) :
    reply (reply state now serial response) now serial response =
      reply state now serial response := by
  cases pending : state.pending with
  | none => simp [reply, pending]
  | some snap =>
      by_cases wrong : serial ≠ snap.serial
      · simp [reply, pending, wrong]
      · by_cases fresh : current state snap = true
        · simp [reply, pending, wrong, fresh, handle_reply_consumes_provider_slot]
        · simp [reply, pending, wrong, fresh]

theorem fulfillment_requires_matching_observed_accepted_result
    (accepts : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (key : ConversationContinuation.RequestKey)
    (receipt : ConversationContinuation.Receipt)
    (changed : (finish accepts state key receipt).requests.commitments key ≠
      state.requests.commitments key) :
    receipt.ticket.request = key ∧ receipt ∈ state.requests.journal ∧
    receipt.ticket ∈ state.requests.observed ∧ receipt.successful = true ∧
    accepts key receipt = true := by
  have admitted : ConversationContinuation.canComplete accepts state.requests key receipt = true := by
    unfold finish at changed
    split at changed
    · unfold ConversationContinuation.complete at changed
      split at changed
      · assumption
      · exact False.elim (changed rfl)
    · exact False.elim (changed rfl)
  exact (ConversationContinuation.completion_requires_matching_observed_success
    accepts state.requests key receipt admitted).2

theorem finish_cannot_discharge_another_request
    (accepts : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (key other : ConversationContinuation.RequestKey)
    (receipt : ConversationContinuation.Receipt) (different : other ≠ key) :
    (finish accepts state key receipt).requests.commitments other =
      state.requests.commitments other := by
  unfold finish
  split
  · exact ConversationContinuation.complete_preserves_other_work
      accepts state.requests key other receipt different
  · rfl

theorem dependent_precommitment_requires_observation_invariance
    {Observation Continuation : Type _} [Inhabited Observation]
    (required : Observation → Continuation) :
    (∃ fixed, PettaClaw.FeedbackSensitiveBatch.PrecommitmentCorrect required fixed) ↔
      PettaClaw.FeedbackSensitiveBatch.ObservationInvariant required :=
  PettaClaw.FeedbackSensitiveBatch.precommitment_exists_iff_observation_invariant required

/-! ## Preservation over arbitrary operational traces -/

theorem handle_reply_preserves_active_work (state : State) (now : Int)
    (snap : Snapshot) (response : Reply) (key : ConversationContinuation.RequestKey)
    (active : state.requests.commitments key = .active) :
    (handleReply state now snap response).requests.commitments key = .active := by
  cases response with
  | failure => exact active
  | text => exact active
  | command ticket tool =>
      cases admitted : admitEffect state snap ticket tool with
      | none => simpa [handleReply, admitted] using active
      | some dispatch =>
          simp only [handleReply, admitted]
          split
          · simpa [ConversationContinuation.proposal_preserves_work] using active
          · exact active

theorem reply_preserves_active_work (state : State) (now : Int) (serial : Nat)
    (response : Reply) (key : ConversationContinuation.RequestKey)
    (active : state.requests.commitments key = .active) :
    (reply state now serial response).requests.commitments key = .active := by
  cases pending : state.pending with
  | none => simpa [reply, pending] using active
  | some snap =>
      simp only [reply, pending]
      split
      · exact active
      · split
        · exact handle_reply_preserves_active_work state now snap response key active
        · exact active

theorem report_preserves_active_work (state : State)
    (receipt : ConversationContinuation.Receipt) (key : ConversationContinuation.RequestKey)
    (active : state.requests.commitments key = .active) :
    (report state receipt).requests.commitments key = .active := by
  cases dispatched : state.dispatch with
  | none => simpa [report, dispatched] using active
  | some dispatch =>
      simp only [report, dispatched]
      split
      · simpa [ConversationContinuation.broker_return_does_not_complete_work] using active
      · exact active

inductive OperationalEvent where
  | delivered (key : ConversationContinuation.RequestKey)
  | acknowledged (key : ConversationContinuation.RequestKey)
  | paused
  | resumed
  | modeSelected (mode : Mode)
  | routerReplaced (router : CodingAgent.RequestView)
  | compacted (budget : Nat)
  | captured (now : Int) (focus : ConversationContinuation.RequestKey)
      (changes : List IterArchitecture.Transformation)
  | replied (now : Int) (serial : Nat) (response : Reply)
  | reported (receipt : ConversationContinuation.Receipt)
  | observed (ticket : ConversationContinuation.Ticket)
  | rested (deadline : Int)
  | woke (now : Int)
  | restarted

def step (state : State) : OperationalEvent → State
  | .delivered key => deliver state key
  | .acknowledged key => acknowledge state key
  | .paused => pause state
  | .resumed => resume state
  | .modeSelected mode => selectMode state mode
  | .routerReplaced router => replaceRouter state router
  | .compacted budget => compact state budget
  | .captured now focus changes => capture state now focus changes
  | .replied now serial response => reply state now serial response
  | .reported receipt => report state receipt
  | .observed ticket => observe state ticket
  | .rested deadline => cooldown state deadline
  | .woke now => omegaWake state now
  | .restarted => restore state

def run : State → List OperationalEvent → State
  | state, [] => state
  | state, event :: events => run (step state event) events

theorem operational_step_preserves_active_work (state : State)
    (event : OperationalEvent) (key : ConversationContinuation.RequestKey)
    (active : state.requests.commitments key = .active) :
    (step state event).requests.commitments key = .active := by
  cases event with
  | delivered input =>
      simp only [step, deliver]
      split
      · exact active
      · exact ConversationContinuation.accept_preserves_active_work state.requests input key active
  | acknowledged input =>
      simpa [step, acknowledge, ConversationContinuation.acknowledgement_preserves_work] using active
  | paused => exact active
  | resumed => exact active
  | modeSelected mode => exact active
  | routerReplaced router => exact active
  | compacted budget => exact active
  | captured now focus changes => simpa [step, capture_preserves_request_ledger] using active
  | replied now serial response => exact reply_preserves_active_work state now serial response key active
  | reported receipt => exact report_preserves_active_work state receipt key active
  | observed ticket =>
      simpa [step, observe, ConversationContinuation.observed_result_does_not_complete_work] using active
  | rested deadline => exact active
  | woke now => exact active
  | restarted => exact active

theorem arbitrary_operational_trace_preserves_unfinished_work (state : State)
    (events : List OperationalEvent) (key : ConversationContinuation.RequestKey)
    (active : state.requests.commitments key = .active) :
    (run state events).requests.commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih =>
      exact ih (step state event)
        (operational_step_preserves_active_work state event key active)

theorem handle_reply_preserves_accepted_request (state : State) (now : Int)
    (snap : Snapshot) (response : Reply) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted) :
    key ∈ (handleReply state now snap response).requests.accepted := by
  cases response with
  | failure => exact present
  | text => exact present
  | command ticket tool =>
      cases admitted : admitEffect state snap ticket tool with
      | none => simpa [handleReply, admitted] using present
      | some dispatch =>
          simp only [handleReply, admitted]
          split
          · exact ConversationContinuation.control_step_preserves_accepted_request
              state.requests (.proposed ticket) key present
          · exact present

theorem reply_preserves_accepted_request (state : State) (now : Int) (serial : Nat)
    (response : Reply) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted) :
    key ∈ (reply state now serial response).requests.accepted := by
  cases pending : state.pending with
  | none => simpa [reply, pending] using present
  | some snap =>
      simp only [reply, pending]
      split
      · exact present
      · split
        · exact handle_reply_preserves_accepted_request state now snap response key present
        · exact present

theorem report_preserves_accepted_request (state : State)
    (receipt : ConversationContinuation.Receipt) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted) :
    key ∈ (report state receipt).requests.accepted := by
  cases dispatched : state.dispatch with
  | none => simpa [report, dispatched] using present
  | some dispatch =>
      simp only [report, dispatched]
      split
      · exact ConversationContinuation.control_step_preserves_accepted_request
          state.requests (.returned receipt) key present
      · exact present

theorem operational_step_preserves_accepted_request (state : State)
    (event : OperationalEvent) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted) :
    key ∈ (step state event).requests.accepted := by
  cases event with
  | delivered input =>
      simp only [step, deliver]
      split
      · exact present
      · exact ConversationContinuation.control_step_preserves_accepted_request
          state.requests (.accepted input) key present
  | acknowledged input =>
      exact ConversationContinuation.control_step_preserves_accepted_request
        state.requests (.acknowledged input) key present
  | paused => exact present
  | resumed => exact present
  | modeSelected mode => exact present
  | routerReplaced router => exact present
  | compacted budget => exact present
  | captured now focus changes =>
      simpa [step, capture_preserves_request_ledger] using present
  | replied now serial response =>
      exact reply_preserves_accepted_request state now serial response key present
  | reported receipt => exact report_preserves_accepted_request state receipt key present
  | observed ticket =>
      exact ConversationContinuation.control_step_preserves_accepted_request
        state.requests (.observed ticket) key present
  | rested deadline => exact present
  | woke now => exact present
  | restarted => exact present

theorem arbitrary_operational_trace_preserves_accepted_request (state : State)
    (events : List OperationalEvent) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted) :
    key ∈ (run state events).requests.accepted := by
  induction events generalizing state with
  | nil => exact present
  | cons event events ih =>
      exact ih (step state event)
        (operational_step_preserves_accepted_request state event key present)

theorem unfinished_request_blocks_empty_work_claim_after_any_trace (state : State)
    (events : List OperationalEvent) (key : ConversationContinuation.RequestKey)
    (present : key ∈ state.requests.accepted)
    (active : state.requests.commitments key = .active) :
    ConversationContinuation.idleAllowed (run state events).requests = false :=
  ConversationContinuation.active_request_blocks_idle _ key
    (arbitrary_operational_trace_preserves_accepted_request state events key present)
    (arbitrary_operational_trace_preserves_unfinished_work state events key active)

end ObservedStrategy
