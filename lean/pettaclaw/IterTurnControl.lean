/-!
# IterTurnControl — progress checkpoints and provider-error handling

Two loop changes in `bgoertzel-sing/iter` master (`3399366`) and its
branches.

**Checkpoints.** After 50 autonomous steps the reference loop rests
(`IterArchitecture.finishCycle`). The fork adds a watchdog: when a burst
reaches 50 steps and the model has not called `send` since the last user
input, the loop writes a checkpoint file and sends a short progress message.
Step 45 adds a prompt reminder. A `nop` ends the burst and resets the step
count. The send flag is reset only by new input. The checkpoint is a progress
report, not a recovery point.

**Provider errors.** Commits `2727dbe` and `87374c3` classify HTTP 400, 401,
402, 403 and 413 as terminal: the loop sends one notice, truncates the
transcript to the start of the cycle (before the user's input was appended),
and waits for new input, even when the notice could not be delivered. Every
other error is retried after one second. Branch
`agent/protocosmo2-multi-branch` (`6ea3dd6`) adds exponential backoff for
transient errors (timeouts, 408, 409, 429, 5xx): base 5 s, doubled per failure,
capped at 300 s, with an idle state after three capped waits or a quota
message. Errors that are neither terminal nor transient keep the one-second
retry.

Results:
* `silent_burst_checkpoints`: a burst with no `send` since the input produces a
  checkpoint message at its 50th step.
* `acknowledgement_disables_checkpoints`: after a single `send`, any number of
  later steps pass without a message, so one early acknowledgement turns the
  watchdog off until the next input.
* `nop_resets_without_message`: bursts of 49 steps ended by `nop` never
  trigger a checkpoint.
* `quiet_bounded` (fix): counting working steps since the last visible message,
  with `nop` neither counting nor resetting, keeps silence below 50 working
  steps on every trace.
* `transient_errors_idle_at_ninth`: nine consecutive transient errors reach the
  idle state; earlier ones wait 5, 10, …, 160, 300, 300 seconds.
* `other_errors_retry_forever`: an error that is neither terminal nor transient
  (for example HTTP 404) is retried every second forever; the backoff state
  never changes.
* `terminal_error_drops_input`: the terminal path truncates the transcript
  before the user's message, so if the notice also fails nothing records the
  request. Retrying from the post-input checkpoint keeps it
  (`IterArchitecture.rollback_preserves_checkpoint`).
* `budgeted_errors_leave_retry` (fix): with one budget for consecutive failures
  of every class, any error stream leaves the retry state within the budget.

A CeTTa-native loop keeps the unanswered request in its request ledger with a
failure receipt instead of truncating it away; the user notice is its own
retried effect. One failure budget covers every error class, and progress
reports are owed per working step since the last visible message.
-/

namespace IterTurnControl

/-! ## The checkpoint watchdog -/

def maxFastSteps : Nat := 50

/-- Steps in the current burst and whether `send` was called since the last
input. -/
structure Watch where
  steps : Nat
  sent : Bool
deriving Repr, DecidableEq

inductive Call
  | send
  | nop
  | work
deriving Repr, DecidableEq

/-- One cycle: optional input, then one tool call. Returns the next state and
whether the user saw a message (a `send` or a checkpoint). -/
def cycle (w : Watch) (input : Bool) (c : Call) : Watch × Bool :=
  let sent := (if input then false else w.sent) || c == .send
  let steps := if input then 0 else w.steps + 1
  match c with
  | .nop => (⟨0, sent⟩, false)
  | _ =>
      if maxFastSteps ≤ steps then (⟨0, sent⟩, c == .send || !sent)
      else (⟨steps, sent⟩, c == .send)

/-- Run cycles without input; collect the visibility flags. -/
def run (w : Watch) : List Call → Watch × List Bool
  | [] => (w, [])
  | c :: rest =>
      let r := run (cycle w false c).1 rest
      (r.1, (cycle w false c).2 :: r.2)

theorem silent_burst_checkpoints :
    (run ⟨0, false⟩ (List.replicate 50 .work)).2 =
      List.replicate 49 false ++ [true] := by
  decide

theorem acknowledgement_disables_checkpoints (n : Nat) (w : Watch) (hs : w.sent = true) :
    (run w (List.replicate n .work)).2 = List.replicate n false := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    have hstep : (cycle w false .work).2 = false ∧ (cycle w false .work).1.sent = true := by
      unfold cycle
      simp only [hs, Bool.false_eq_true, if_false]
      split <;> simp
    simp only [List.replicate_succ, run]
    rw [hstep.1, ih _ hstep.2]

/-- One round: 49 working steps, then `nop`. -/
def round : List Call := List.replicate 49 .work ++ [.nop]

set_option maxRecDepth 8000 in
theorem round_silent :
    run ⟨0, false⟩ round = (⟨0, false⟩, List.replicate 50 false) := by
  decide

theorem run_append (w : Watch) (xs ys : List Call) :
    run w (xs ++ ys) = ((run (run w xs).1 ys).1, (run w xs).2 ++ (run (run w xs).1 ys).2) := by
  induction xs generalizing w with
  | nil => rfl
  | cons c rest ih => simp [run, ih]

theorem nop_resets_without_message (k : Nat) :
    (run ⟨0, false⟩ ((List.replicate k round).flatten)).2 =
      List.replicate (50 * k) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, run_append, round_silent]
    simp only
    rw [ih, Nat.mul_succ, Nat.add_comm (50 * k) 50, List.replicate_append_replicate]

/-- The fix: count working steps since the last visible message. A `nop`
neither counts nor resets; input does not reset either. -/
def quietCycle (quiet : Nat) (c : Call) : Nat × Bool :=
  match c with
  | .send => (0, true)
  | .nop => (quiet, false)
  | .work => if maxFastSteps ≤ quiet + 1 then (0, true) else (quiet + 1, false)

theorem quiet_cycle_bounded (quiet : Nat) (c : Call) (h : quiet < maxFastSteps) :
    (quietCycle quiet c).1 < maxFastSteps := by
  unfold quietCycle maxFastSteps at *
  split
  · decide
  · exact h
  · split <;> simp <;> omega

/-- On every trace, fewer than 50 working steps pass without a visible message. -/
theorem quiet_bounded (cs : List Call) :
    ∀ q, q < maxFastSteps → (cs.foldl (fun q c => (quietCycle q c).1) q) < maxFastSteps := by
  induction cs with
  | nil => intro q h; exact h
  | cons c rest ih => intro q h; exact ih _ (quiet_cycle_bounded q c h)

/-! ## Provider errors -/

inductive Err
  | terminal
  | transient
  | quota
  | other
deriving Repr, DecidableEq

inductive Outcome
  | retry (wait : Nat)
  | idle
  | abort
deriving Repr, DecidableEq

/-- Consecutive transient failures and consecutive capped waits. -/
structure Backoff where
  failures : Nat
  capped : Nat
deriving Repr, DecidableEq

def baseDelay : Nat := 5
def capDelay : Nat := 300

/-- `retry_backoff_delay` without jitter. -/
def delay (n : Nat) : Nat := min (baseDelay * 2 ^ (n - 1)) capDelay

/-- The multi-branch error handler. -/
def onError (s : Backoff) : Err → Backoff × Outcome
  | .terminal => (⟨0, 0⟩, .abort)
  | .quota => (⟨0, 0⟩, .idle)
  | .transient =>
      let n := s.failures + 1
      let d := delay n
      let c := if capDelay ≤ d then s.capped + 1 else 0
      if 3 ≤ c then (⟨0, 0⟩, .idle) else (⟨n, c⟩, .retry d)
  | .other => (s, .retry 1)

def runErrors (s : Backoff) : List Err → List Outcome
  | [] => []
  | e :: rest => (onError s e).2 :: runErrors (onError s e).1 rest

theorem transient_errors_idle_at_ninth :
    runErrors ⟨0, 0⟩ (List.replicate 9 .transient) =
      [.retry 5, .retry 10, .retry 20, .retry 40, .retry 80, .retry 160, .retry 300,
        .retry 300, .idle] := by
  decide

theorem other_errors_retry_forever (s : Backoff) (n : Nat) :
    runErrors s (List.replicate n .other) = List.replicate n (.retry 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, runErrors, onError, ih]

/-- The terminal path truncates to the start of the cycle, before the user's
input was appended. -/
def terminalTruncate (transcript : List Nat) (turnStart : Nat) : List Nat :=
  transcript.take turnStart

theorem terminal_error_drops_input (before : List Nat) (input : Nat) (attempt : List Nat) :
    input ∉ before → input ∉ terminalTruncate (before ++ input :: attempt) before.length := by
  intro h
  simp [terminalTruncate, List.take_left' rfl, h]

/-- The fix: one budget for consecutive failures of every class. -/
def onErrorBudget (budget failures : Nat) : Err → Nat × Outcome
  | .terminal => (0, .abort)
  | _ => if budget ≤ failures + 1 then (0, .idle) else (failures + 1, .retry 1)

def runBudget (budget failures : Nat) : List Err → List Outcome
  | [] => []
  | e :: rest =>
      (onErrorBudget budget failures e).2 ::
        runBudget budget (onErrorBudget budget failures e).1 rest

def leaves : Outcome → Bool
  | .retry _ => false
  | _ => true

/-- Any stream of `budget` consecutive errors leaves the retry state. -/
theorem budgeted_errors_leave_retry (budget : Nat) (hb : 0 < budget) (errs : List Err)
    (hlen : errs.length = budget) : (runBudget budget 0 errs).any leaves = true := by
  have key : ∀ (f : Nat) (es : List Err), f < budget → budget ≤ f + es.length →
      (runBudget budget f es).any leaves = true := by
    intro f es
    induction es generalizing f with
    | nil => intro h1 h2; simp at h2; omega
    | cons e rest ih =>
      intro h1 h2
      simp only [List.length_cons] at h2
      cases e with
      | terminal => simp [runBudget, onErrorBudget, leaves]
      | transient | quota | other =>
        simp only [runBudget, onErrorBudget]
        split
        · simp [leaves]
        · rename_i hlt
          simp only [List.any_cons, leaves, Bool.false_or]
          exact ih (f + 1) (by omega) (by omega)
  exact key 0 errs hb (by omega)

end IterTurnControl

/-! ## Axiom audit -/
#print axioms IterTurnControl.silent_burst_checkpoints
#print axioms IterTurnControl.acknowledgement_disables_checkpoints
#print axioms IterTurnControl.round_silent
#print axioms IterTurnControl.run_append
#print axioms IterTurnControl.nop_resets_without_message
#print axioms IterTurnControl.quiet_cycle_bounded
#print axioms IterTurnControl.quiet_bounded
#print axioms IterTurnControl.transient_errors_idle_at_ninth
#print axioms IterTurnControl.other_errors_retry_forever
#print axioms IterTurnControl.terminal_error_drops_input
#print axioms IterTurnControl.budgeted_errors_leave_retry
