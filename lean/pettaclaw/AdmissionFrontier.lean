import Std

/-!

Historical/design model: this file records a policy studied before the sequential
tool simplification. Its holds, quotas, or scheduling assumptions are not the
current dispatch contract. See `SequentialTools.lean` for that contract and
`CommandHolds.lean` for the conditional costs of the removed hold policy.
# Independent provider and effect admission

The host classifies the actually admitted command prefix using trusted
observation contracts. An undeclared command is an effect. Classification is
an assumption about the tool implementation, not something a name proves.

This executable model separates a provider slot from the frontier of unresolved
effects. It preserves unknown outcomes without making every unknown outcome a
barrier to thought. Liveness below is local and conditional on admission being
enabled; no theorem promises a provider response, a successful task, or recovery
of a lost receipt. Correlated ownership, routing and snapshot checks remain
separate preconditions, represented by `authorized` and `current`.
-/

namespace AdmissionFrontier

inductive Kind where | observation | effect
  deriving DecidableEq, Repr

inductive Status where | issued | uncertain | returned
  deriving DecidableEq, Repr

structure Attempt where
  ticket : Nat
  kind : Kind
  status : Status
  receipt : Bool := false
  observed : Bool := false
  deriving DecidableEq, Repr

def outstanding (a : Attempt) : Bool :=
  match a.status with
  | .issued | .uncertain => true
  | .returned => a.receipt && !a.observed

def blocker (a : Attempt) : Bool := outstanding a && decide (a.kind = .effect)

def mayIssue (rows : List Attempt) (kind : Kind) (exclude : Option Nat := none) : Bool :=
  decide (kind = .observation) ||
    !(rows.any fun a => decide (some a.ticket ≠ exclude) && blocker a)

-- A deferred suffix has no execution authority. Malformed/empty prefixes
-- conservatively classify as effects, as do undeclared host operations.
def prefixKind (commands : List Kind) (limit : Nat) : Kind :=
  let selected := commands.take limit
  if !selected.isEmpty && selected.all (fun k => decide (k = .observation)) then
    .observation else .effect

inductive Denial where
  | unavailable | paused | pending | allowance | cooldown
  deriving DecidableEq, Repr, Inhabited

structure Controls where
  available : Bool := true
  paused : Bool := false
  pending : Option Nat := none
  allowance : Option Nat := none
  cooldown : Nat := 0
  now : Nat := 0
  deriving DecidableEq, Repr

def thoughtDenial (c : Controls) : Option Denial :=
  if !c.available then some .unavailable
  else if c.paused then some .paused
  else if c.pending.isSome then some .pending
  else if c.allowance.any (fun n => n = 0) then some .allowance
  else if c.now < c.cooldown then some .cooldown
  else none

structure State where
  controls : Controls := {}
  next : Nat := 0
  rows : List Attempt := []
  deriving DecidableEq, Repr, Inhabited

def capture (s : State) : Option State :=
  if thoughtDenial s.controls = none then
    some { s with
      next := s.next + 1
      controls := { s.controls with
        pending := some s.next
        allowance := s.controls.allowance.map (· - 1) } }
  else none

def issue (s : State) (kind : Kind) (current authorized : Bool := true) : State :=
  match s.controls.pending with
  | none => s
  | some ticket =>
    let ready := { s with controls := { s.controls with pending := none } }
    if current && authorized && mayIssue s.rows kind then
      { ready with rows := s.rows ++ [{ ticket, kind, status := .issued }] }
    else ready

def restart (s : State) : State :=
  { s with
    controls := { s.controls with pending := none }
    rows := s.rows.map fun a =>
      if a.status = .issued then { a with status := .uncertain } else a }

def report (s : State) (ticket : Nat) : State :=
  { s with rows := s.rows.map fun a =>
    if a.ticket = ticket && !a.receipt && outstanding a then
      { a with status := .returned, receipt := true } else a }

def observe (s : State) (ticket : Nat) (exactDigest : Bool) : State :=
  { s with rows := s.rows.map fun a =>
    if a.ticket = ticket && a.receipt && exactDigest then
      { a with observed := true } else a }

-- This is the old policy's causal barrier, independent of provider state.
def oldThoughtAllowed (s : State) : Bool :=
  decide (thoughtDenial s.controls = none) && !s.rows.any outstanding

def unknownRead : State :=
  { rows := [{ ticket := 0, kind := .observation, status := .uncertain }] }

def unknownEffect : State :=
  { rows := [{ ticket := 0, kind := .effect, status := .uncertain }] }

theorem old_policy_stalls_on_missing_read : oldThoughtAllowed unknownRead = false := by decide

def oldRetry : Nat → State → State
  | 0, s => s
  | n + 1, s =>
    let previous := oldRetry n s
    if oldThoughtAllowed previous then { previous with next := previous.next + 1 } else previous

theorem old_policy_retry_cannot_change_the_barrier (n : Nat) :
    oldRetry n unknownRead = unknownRead := by
  induction n with
  | zero => rfl
  | succ n ih => simp [oldRetry, ih, old_policy_stalls_on_missing_read]

theorem thinking_independent_of_effect_history (s : State) (rows : List Attempt) :
    (capture { s with rows := rows }).isSome = (capture s).isSome := by
  simp only [capture]
  split <;> rfl

theorem enabled_thinking_has_a_successor (s : State)
    (h : thoughtDenial s.controls = none) : (capture s).isSome = true := by
  simp [capture, h]

theorem disabled_thinking_cannot_admit (s : State)
    (h : thoughtDenial s.controls ≠ none) : capture s = none := by
  simp [capture, h]

theorem capture_preserves_unknown_outcomes (s t : State) (h : capture s = some t) :
    t.rows = s.rows := by
  unfold capture at h
  split at h
  · cases h; rfl
  · contradiction

theorem capture_has_one_owned_provider_slot (s t : State) (h : capture s = some t) :
    t.controls.pending = some s.next ∧ t.next = s.next + 1 := by
  unfold capture at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · contradiction

theorem pending_provider_prevents_duplicate_capture (s : State)
    (h : s.controls.pending.isSome = true) : capture s = none := by
  simp only [capture, thoughtDenial, h]
  split <;> simp_all
  split <;> simp_all

theorem observations_remain_admissible (rows : List Attempt) (exclude : Option Nat) :
    mayIssue rows .observation exclude = true := by simp [mayIssue]

theorem unresolved_effect_prevents_mutation (rows : List Attempt)
    (h : rows.any blocker = true) : mayIssue rows .effect = false := by
  simpa [mayIssue] using congrArg Bool.not h

theorem blocked_mutation_cannot_issue (s : State) (current authorized : Bool)
    (h : mayIssue s.rows .effect = false) :
    (issue s .effect current authorized).rows = s.rows := by
  cases hp : s.controls.pending <;> simp [issue, hp, h]

theorem fresh_thought_can_follow_missing_read : (capture unknownRead).isSome = true := by decide

theorem fresh_thought_can_follow_missing_effect : (capture unknownEffect).isSome = true := by decide

theorem missing_effect_still_blocks_mutation : mayIssue unknownEffect.rows .effect = false := by decide

theorem missing_read_does_not_block_mutation : mayIssue unknownRead.rows .effect = true := by decide

theorem stale_or_unauthorized_reply_has_no_new_effect (s : State)
    (kind : Kind) : (issue s kind false).rows = s.rows ∧
                    (issue s kind true false).rows = s.rows := by
  cases hp : s.controls.pending <;> simp [issue, hp]

theorem restart_preserves_receipts_and_observation (s : State) :
    (restart s).rows.map (fun a => (a.ticket, a.receipt, a.observed)) =
      s.rows.map (fun a => (a.ticket, a.receipt, a.observed)) := by
  simp [restart]
  intro a _
  split <;> simp

theorem restart_releases_provider_slot (s : State) : (restart s).controls.pending = none := rfl

theorem inexact_observation_cannot_change_outcomes (s : State) (ticket : Nat) :
    observe s ticket false = s := by
  simp [observe]

theorem returned_unobserved_effect_blocks :
    mayIssue [{ ticket := 0, kind := .effect, status := .returned,
                receipt := true, observed := false }] .effect = false := by decide

theorem exact_observation_releases_returned_effect :
    mayIssue (observe (report unknownEffect 0) 0 true).rows .effect = true := by decide

theorem forged_observation_keeps_effect_blocked :
    mayIssue (observe (report unknownEffect 0) 0 false).rows .effect = false := by decide

theorem reporting_without_observation_does_not_release_effect :
    mayIssue (report unknownEffect 0).rows .effect = false := by decide

theorem deferred_effect_has_no_authority :
    prefixKind [.observation, .effect] 1 = .observation := by decide

theorem admitted_effect_cannot_hide_in_read_batch :
    prefixKind [.observation, .effect] 2 = .effect := by decide

theorem empty_prefix_has_no_observation_contract (commands : List Kind) :
    prefixKind commands 0 = .effect := by simp [prefixKind]

-- Executable projections consumed by the host correspondence runner.
def projection (s : State) : List Nat :=
  [s.next, if s.controls.pending.isSome then 1 else 0, s.rows.length,
   (s.rows.filter fun a => decide (a.status = .uncertain)).length,
   (s.rows.filter (·.receipt)).length, (s.rows.filter (·.observed)).length,
   if (capture s).isSome then 1 else 0, if mayIssue s.rows .effect then 1 else 0]

def start : State := {}
def issuedRead : State := issue (capture start).get! .observation
def issuedEffect : State := issue (capture start).get! .effect
def readRestart : State := restart issuedRead
def effectRestart : State := restart issuedEffect
def blockedEffect : State := issue (capture effectRestart).get! .effect
def replayStates : List State :=
  [readRestart,
   issue (capture readRestart).get! .effect,
   effectRestart,
   blockedEffect,
   issue (capture blockedEffect).get! .observation,
   report effectRestart 0,
   observe (report effectRestart 0) 0 false,
   observe (report effectRestart 0) 0 true,
   issue (capture (observe (report effectRestart 0) 0 true)).get! .effect]

def replayProjections : List (List Nat) := replayStates.map projection

end AdmissionFrontier
