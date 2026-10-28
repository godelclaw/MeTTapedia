/-!
# WorkLease — budgeted work leases for long-horizon autonomy

`bgoertzel-sing/iter-work-lease-controller` (`ccbaa30`) proposes replacing a
fixed per-event cap on provider calls with a transactional work lease. An
inbound event admits a lease for its bot. Every provider call must first
reserve a turn and its worst-case tokens; finishing the turn reconciles the
tokens and updates error and no-progress counters. Every ten turns a review is
due; a cheap reviewer classifies the recent turns as productive, uncertain or
pathological, and a confident pathology pauses the lease. Only an explicit
human renewal adds budget. Side effects are journaled as prepared, executing,
confirmed, failed or uncertain, and completion is refused while one is prepared
or executing.

The model keeps the controller's counters and status, abstracting time, SQLite
transactions and the reviewer.

Results:
* `turns_monotone` and `turns_within_budget` (safety, every trace): the turn
  count never decreases and never exceeds the current turn budget, which only
  a renewal raises (`renew_adds_exactly`). `tokens_within_budget`: reserved
  plus reconciled tokens stay within the token budget.
* `paused_lease_reserves_nothing`: after a confident pathology verdict, or any
  other pause, no turn is reserved until a renewal.
* `review_gate_is_reservation_only`: the review gate blocks turn 11 until a
  review is *reserved*, not until it is decided. With a review reserved and no
  verdict, turn 11 is authorized. `pending_review_blocks_turns` (fix): denying
  turns while a review is pending makes the verdict precede further work.
* `admit_idempotent` and `one_active_lease`: replaying an event changes
  nothing, and a bot never holds two active leases.
* `paused_lease_admits_new_event`: a paused lease does not block a new event,
  which opens a fresh lease with fresh counters. The bound is per admitted
  event, so messages that agents send each other can extend autonomy.
* `completes_with_uncertain_effect`: completion is refused while an effect is
  prepared or executing, but allowed while one is uncertain.

The lease kernel is sound for what it claims about counters. In CeTTa the lease,
turns, reviews and effect intents are atoms in the agent's log, reserved in one
transaction with the request ledger (`EventSourcedMemory.lean`), a review
verdict is an atom that turns after the review boundary depend on, and
completion requires every effect to be settled and a correlated receipt, as in
`ConversationContinuation.lean`.
-/

namespace WorkLease

structure Budget where
  maxTurns : Nat
  maxTokens : Nat
  maxErrors : Nat
  maxNoProgress : Nat
  reviewEvery : Nat
  maxReviews : Nat
  uncertainContinuation : Nat
deriving Repr, DecidableEq

inductive Status
  | active
  | completed
  | pausedBudget
  | pausedPathology
deriving Repr, DecidableEq

structure Lease where
  status : Status
  turns : Nat
  tokens : Nat
  errors : Nat
  noProgress : Nat
  reviews : Nat
  lastReview : Nat
  weak : Nat
  budget : Budget
  pendingReview : Bool
deriving Repr, DecidableEq

/-- `reserve_turn`: denial reasons in the controller's order. Budget denials
pause the lease; a due review only denies. `gate` selects whether a pending
review also denies (the fix). -/
def reserveTurn (gate : Bool) (l : Lease) (reserve : Nat) : Lease :=
  if l.status ≠ .active then l
  else if l.budget.maxTurns ≤ l.turns ∨ l.budget.maxTokens < l.tokens + reserve ∨
      l.budget.maxErrors ≤ l.errors ∨ l.budget.maxNoProgress ≤ l.noProgress then
    { l with status := .pausedBudget }
  else if l.budget.reviewEvery ≤ l.turns - l.lastReview then l
  else if gate && l.pendingReview then l
  else { l with turns := l.turns + 1, tokens := l.tokens + reserve }

/-- `finish_turn`: reconcile tokens downward; a report above the reservation is
rejected. -/
def finishTurn (l : Lease) (reserve actual : Nat) (error progress : Bool) : Lease :=
  if reserve < actual then l
  else { l with tokens := l.tokens - (reserve - actual),
                errors := l.errors + (if error then 1 else 0),
                noProgress := if progress then 0 else l.noProgress + 1 }

/-- `reserve_review`. -/
def reserveReview (l : Lease) : Lease :=
  if l.status ≠ .active ∨ l.turns - l.lastReview < l.budget.reviewEvery then l
  else if l.budget.maxReviews ≤ l.reviews then { l with status := .pausedBudget }
  else { l with reviews := l.reviews + 1, lastReview := l.turns, pendingReview := true }

inductive Verdict
  | productive
  | uncertain
  | pathology (confident : Bool)
deriving Repr, DecidableEq

/-- `finish_review`. -/
def finishReview (l : Lease) (v : Verdict) : Lease :=
  let l := { l with pendingReview := false }
  match v with
  | .productive => l
  | .uncertain =>
      { l with lastReview := l.lastReview + l.budget.uncertainContinuation - l.budget.reviewEvery }
  | .pathology confident =>
      if confident ∨ 1 ≤ l.weak then { l with status := .pausedPathology }
      else { l with weak := l.weak + 1 }

/-- `fail_review`. -/
def failReview (l : Lease) : Lease := { l with status := .pausedBudget, pendingReview := false }

/-- `renew`: a human adds turns, tokens and reviews to a paused lease. Totals are
kept; error and progress counters and the review anchor are reset. -/
def renew (l : Lease) (dTurns dTokens dReviews : Nat) : Lease :=
  if l.status = .pausedBudget ∨ l.status = .pausedPathology then
    { l with status := .active, errors := 0, noProgress := 0, lastReview := l.turns,
             pendingReview := false,
             budget := { l.budget with maxTurns := l.budget.maxTurns + dTurns,
                                       maxTokens := l.budget.maxTokens + dTokens,
                                       maxReviews := l.budget.maxReviews + dReviews } }
  else l

inductive EffectState
  | prepared
  | executing
  | confirmed
  | failed
  | uncertain
deriving Repr, DecidableEq

def openEffect : EffectState → Bool
  | .prepared => true
  | .executing => true
  | _ => false

/-- `complete`: refused while an effect is prepared or executing. -/
def complete (l : Lease) (effects : List EffectState) : Lease :=
  if l.status = .active ∧ !(effects.any openEffect) then { l with status := .completed } else l

inductive Op
  | reserve (tokens : Nat)
  | finish (reserve actual : Nat) (error progress : Bool)
  | reserveReview
  | finishReview (v : Verdict)
  | failReview
  | renew (dTurns dTokens dReviews : Nat)
  | complete (effects : List EffectState)
deriving Repr

def step (gate : Bool) (l : Lease) : Op → Lease
  | .reserve t => reserveTurn gate l t
  | .finish r a e p => finishTurn l r a e p
  | .reserveReview => reserveReview l
  | .finishReview v => finishReview l v
  | .failReview => failReview l
  | .renew a b c => renew l a b c
  | .complete es => complete l es

def run (gate : Bool) (l : Lease) : List Op → Lease
  | [] => l
  | o :: rest => run gate (step gate l o) rest

/-! ## Counters -/

theorem step_turns_monotone (gate : Bool) (l : Lease) (o : Op) : l.turns ≤ (step gate l o).turns := by
  cases o <;> simp only [step, reserveTurn, finishTurn, reserveReview, finishReview, failReview,
    renew, complete] <;> (repeat' split) <;> simp

theorem turns_monotone (gate : Bool) (l : Lease) (ops : List Op) : l.turns ≤ (run gate l ops).turns := by
  induction ops generalizing l with
  | nil => exact Nat.le_refl _
  | cons o rest ih => exact Nat.le_trans (step_turns_monotone gate l o) (ih _)

def WithinBudget (l : Lease) : Prop := l.turns ≤ l.budget.maxTurns ∧ l.tokens ≤ l.budget.maxTokens

theorem step_within_budget (gate : Bool) (l : Lease) (o : Op) (h : WithinBudget l) :
    WithinBudget (step gate l o) := by
  obtain ⟨ht, hk⟩ := h
  cases o with
  | reserve t =>
    simp only [step, reserveTurn]
    split
    · exact ⟨ht, hk⟩
    · split
      · exact ⟨ht, hk⟩
      · rename_i hno
        split
        · exact ⟨ht, hk⟩
        · split
          · exact ⟨ht, hk⟩
          · simp only [not_or, Nat.not_le, Nat.not_lt] at hno
            exact ⟨by simp; omega, by simp; omega⟩
  | finish r a e p =>
    simp only [step, finishTurn]
    split
    · exact ⟨ht, hk⟩
    · exact ⟨ht, by simp; omega⟩
  | reserveReview =>
    simp only [step, reserveReview]
    split
    · exact ⟨ht, hk⟩
    · split <;> exact ⟨ht, hk⟩
  | finishReview v =>
    simp only [step, finishReview]
    cases v with
    | productive => exact ⟨ht, hk⟩
    | uncertain => exact ⟨ht, hk⟩
    | pathology c =>
      by_cases hc : c = true ∨ 1 ≤ l.weak
      · simp only [hc, if_true]; exact ⟨ht, hk⟩
      · simp only [hc, if_false]; exact ⟨ht, hk⟩
  | failReview => exact ⟨ht, hk⟩
  | renew a b c =>
    simp only [step, renew]
    split
    · exact ⟨by simp; omega, by simp; omega⟩
    · exact ⟨ht, hk⟩
  | complete es =>
    simp only [step, complete]
    split <;> exact ⟨ht, hk⟩

theorem turns_within_budget (gate : Bool) (l : Lease) (ops : List Op) (h : WithinBudget l) :
    (run gate l ops).turns ≤ (run gate l ops).budget.maxTurns := by
  suffices WithinBudget (run gate l ops) from this.1
  induction ops generalizing l with
  | nil => exact h
  | cons o rest ih => exact ih _ (step_within_budget gate l o h)

theorem tokens_within_budget (gate : Bool) (l : Lease) (ops : List Op) (h : WithinBudget l) :
    (run gate l ops).tokens ≤ (run gate l ops).budget.maxTokens := by
  suffices WithinBudget (run gate l ops) from this.2
  induction ops generalizing l with
  | nil => exact h
  | cons o rest ih => exact ih _ (step_within_budget gate l o h)

theorem renew_adds_exactly (l : Lease) (a b c : Nat) (hp : l.status = .pausedPathology) :
    (renew l a b c).budget.maxTurns = l.budget.maxTurns + a ∧ (renew l a b c).turns = l.turns := by
  simp [renew, hp]

theorem paused_lease_reserves_nothing (gate : Bool) (l : Lease) (t : Nat) (h : l.status ≠ .active) :
    reserveTurn gate l t = l := by
  simp [reserveTurn, h]

/-! ## The review gate -/

def budget10 : Budget := ⟨64, 200000, 5, 4, 10, 8, 2⟩

/-- Ten turns done, no review yet. -/
def tenTurns : Lease := ⟨.active, 10, 1000, 0, 0, 0, 0, 0, budget10, false⟩

theorem review_gate_is_reservation_only :
    (reserveTurn false tenTurns 100).turns = 10 ∧
      (reserveTurn false (reserveReview tenTurns) 100).turns = 11 ∧
      (reserveReview tenTurns).pendingReview = true := by
  decide

theorem pending_review_blocks_turns (l : Lease) (t : Nat) (h : l.pendingReview = true) :
    (reserveTurn true l t).turns = l.turns := by
  unfold reserveTurn
  repeat' split
  all_goals simp_all

/-! ## Admission -/

structure LeaseRow where
  event : Nat
  bot : Nat
  status : Status
deriving Repr, DecidableEq

/-- The controller's `admit`: a replayed event returns its lease; a bot with an
active lease is refused; otherwise a new active lease is created. -/
def admitEvent (rows : List LeaseRow) (event bot : Nat) : List LeaseRow :=
  if rows.any (fun r => r.event == event) then rows
  else if rows.any (fun r => r.bot == bot && r.status == .active) then rows
  else ⟨event, bot, .active⟩ :: rows

theorem admit_idempotent (rows : List LeaseRow) (event bot : Nat) :
    admitEvent (admitEvent rows event bot) event bot = admitEvent rows event bot := by
  unfold admitEvent
  by_cases h1 : rows.any (fun r => r.event == event) = true
  · simp [h1]
  · by_cases h2 : rows.any (fun r => r.bot == bot && r.status == .active) = true
    · simp [h1, h2]
    · simp [h1, h2]

def activeCount (rows : List LeaseRow) (bot : Nat) : Nat :=
  (rows.filter (fun r => r.bot == bot && r.status == .active)).length

theorem one_active_lease (rows : List LeaseRow) (event bot b : Nat)
    (h : activeCount rows b ≤ 1) : activeCount (admitEvent rows event bot) b ≤ 1 := by
  unfold admitEvent
  split
  · exact h
  · split
    · exact h
    · rename_i _ hnone
      unfold activeCount at h ⊢
      by_cases hb : bot = b
      · subst hb
        have h0 : (rows.filter (fun r => r.bot == bot && r.status == .active)).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro r hr hsat
          exact hnone (List.any_eq_true.mpr ⟨r, hr, hsat⟩)
        simp [h0]
      · simp [hb]
        exact h

theorem paused_lease_admits_new_event :
    admitEvent [⟨1, 7, .pausedPathology⟩] 2 7 = [⟨2, 7, .active⟩, ⟨1, 7, .pausedPathology⟩] := by
  decide

/-! ## Completion -/

theorem completes_with_uncertain_effect :
    (complete tenTurns [.confirmed, .uncertain]).status = .completed ∧
      (complete tenTurns [.executing]).status = .active := by
  decide

end WorkLease

/-! ## Axiom audit -/
#print axioms WorkLease.step_turns_monotone
#print axioms WorkLease.turns_monotone
#print axioms WorkLease.step_within_budget
#print axioms WorkLease.turns_within_budget
#print axioms WorkLease.tokens_within_budget
#print axioms WorkLease.renew_adds_exactly
#print axioms WorkLease.paused_lease_reserves_nothing
#print axioms WorkLease.review_gate_is_reservation_only
#print axioms WorkLease.pending_review_blocks_turns
#print axioms WorkLease.admit_idempotent
#print axioms WorkLease.one_active_lease
#print axioms WorkLease.paused_lease_admits_new_event
#print axioms WorkLease.completes_with_uncertain_effect
