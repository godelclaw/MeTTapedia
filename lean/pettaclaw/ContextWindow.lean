/-!
# ContextWindow — what a running window owes the agent that reads it

The loop rebuilds a fixed-size prompt every turn, so it has no compaction
problem: it cannot overflow, because it never accumulates. Its problem is
the opposite one. For a long time it could see a single turn of its own
results and nothing before that, and it spent whole bursts rediscovering
work it had already done.

A window that fixes that has to promise something, or it will quietly lose
the very thing it was added to carry. The promises here are taken from
`vericore-policy/src/heartbeat_context_policy.rs`, which is Verus-verified
and solved this problem once already:

    spec_recent_turns_within_limit             count <= limit
    spec_reserved_main_turn_preserved          present -> included
    spec_noop_heartbeat_excluded_from_recent   !noop_in_recent
    heartbeat_trace_ok                         bounded, oldest first

The third is load-bearing rather than cosmetic. Six heartbeats answered
with `(nop)` will fill a naive window and evict the only real work in it —
that is not hypothetical, it is what the journal showed on 2026-08-18.

Correspondence (hand-maintained, as in the sibling files): `window` ↔
`helper.recent_actions`; `Turn.substantive` ↔ `not helper._is_noise`;
`Turn.size` ↔ the rendered character count; `limit` ↔ `maxRecentTurns`;
`budget` ↔ the `max_chars` argument.

Scope, stated openly: this is the selection layer. Whether the selected
turns are the *useful* ones is a question about the agent, not about the
window, and it lives above this model.
-/

namespace ContextWindow

/-- One journal turn as the selector sees it. -/
structure Turn where
  id : Nat
  substantive : Bool
  size : Nat
deriving Repr, DecidableEq

def total (l : List Turn) : Nat := (l.map (·.size)).sum

@[simp] theorem total_nil : total [] = 0 := rfl

@[simp] theorem total_cons (t : Turn) (l : List Turn) :
    total (t :: l) = t.size + total l := rfl

/-- Older turns, newest first, admitted only while they fit whole. -/
def admit : Nat → List Turn → List Turn
  | _, [] => []
  | budget, t :: rest =>
      if t.size ≤ budget then t :: admit (budget - t.size) rest else []

/-- The newest turn is admitted unconditionally, truncated to the budget if
it must be: a window that silently drops the most recent action is worse
than a short one. -/
def keep (budget : Nat) : List Turn → List Turn
  | [] => []
  | t :: rest =>
      let head : Turn := { t with size := min t.size budget }
      head :: admit (budget - head.size) rest

/-- The window: substantive turns only, at most `limit` of them, newest
kept, rendered oldest first. Input is oldest first. -/
def window (limit budget : Nat) (turns : List Turn) : List Turn :=
  (keep budget (((turns.filter (·.substantive)).reverse).take limit)).reverse

/-! ## What it promises -/

theorem admit_length : ∀ (b : Nat) (l : List Turn), (admit b l).length ≤ l.length := by
  intro b l
  induction l generalizing b with
  | nil => simp [admit]
  | cons t rest ih =>
    by_cases h : t.size ≤ b
    · simpa [admit, h] using ih (b - t.size)
    · simp [admit, h]

theorem admit_total : ∀ (b : Nat) (l : List Turn), total (admit b l) ≤ b := by
  intro b l
  induction l generalizing b with
  | nil => simp [admit]
  | cons t rest ih =>
    by_cases h : t.size ≤ b
    · have := ih (b - t.size)
      simp [admit, h]
      omega
    · simp [admit, h]

theorem admit_mem : ∀ (b : Nat) (l : List Turn) (x : Turn),
    x ∈ admit b l → x ∈ l := by
  intro b l
  induction l generalizing b with
  | nil => intro x hx; simp [admit] at hx
  | cons t rest ih =>
    intro x hx
    by_cases h : t.size ≤ b
    · rw [admit, if_pos h] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (b - t.size) x hx')
    · rw [admit, if_neg h] at hx; simp at hx

/-- **Bounded.** The window never exceeds its character budget, truncation
of the newest turn included. -/
theorem window_within_budget (limit budget : Nat) (turns : List Turn) :
    total (window limit budget turns) ≤ budget := by
  have key : ∀ l : List Turn, total (keep budget l) ≤ budget := by
    intro l
    cases l with
    | nil => simp [keep]
    | cons t rest =>
      have h := admit_total (budget - min t.size budget) rest
      simp [keep]
      omega
  have rev : ∀ l : List Turn, total l.reverse = total l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      have : total t.reverse = total t := ih
      simp [total, List.sum_append]
      omega
  unfold window
  rw [rev]
  exact key _

/-- **Within the turn limit.** -/
theorem window_within_limit (limit budget : Nat) (turns : List Turn) :
    (window limit budget turns).length ≤ limit := by
  have key : ∀ l : List Turn, (keep budget l).length ≤ l.length := by
    intro l
    cases l with
    | nil => simp [keep]
    | cons t rest =>
      have := admit_length (budget - min t.size budget) rest
      simpa [keep] using this
  unfold window
  rw [List.length_reverse]
  exact Nat.le_trans (key _) (Nat.le_trans (List.length_take_le _ _) (by simp))

/-- **No-op turns never occupy a slot.** The rule that keeps a run of
heartbeat nops from evicting the only real work in the window. -/
theorem window_all_substantive (limit budget : Nat) (turns : List Turn)
    (x : Turn) (hx : x ∈ window limit budget turns) : x.substantive = true := by
  have hkeep : ∀ (l : List Turn) (y : Turn),
      (∀ z ∈ l, z.substantive = true) → y ∈ keep budget l → y.substantive = true := by
    intro l y hl hy
    cases l with
    | nil => simp [keep] at hy
    | cons t rest =>
      rw [keep] at hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hl t (List.mem_cons_self)
      · exact hl y (List.mem_cons_of_mem _ (admit_mem _ rest y hy'))
  have hsub : ∀ z ∈ ((turns.filter (·.substantive)).reverse).take limit,
      z.substantive = true := by
    intro z hz
    have : z ∈ turns.filter (·.substantive) := by
      have := List.mem_of_mem_take hz
      simpa using (List.mem_reverse.mp this)
    simpa using (List.mem_filter.mp this).2
  exact hkeep _ x hsub (by simpa using (List.mem_reverse.mp hx))

/-- **The newest substantive turn is always present.** It is the one the
agent most needs and the one a naive budget check would drop first: it is
admitted before any budget test and truncated rather than omitted. -/
theorem window_keeps_newest (limit budget : Nat) (turns : List Turn)
    (hlim : 0 < limit) (t : Turn) (rest : List Turn)
    (hsrc : (turns.filter (·.substantive)).reverse = t :: rest) :
    ∃ kept ∈ window limit budget turns, kept.id = t.id := by
  refine ⟨{ t with size := min t.size budget }, ?_, rfl⟩
  unfold window
  rw [hsrc]
  cases limit with
  | zero => exact absurd hlim (by simp)
  | succ n =>
    rw [List.take_succ_cons, keep]
    exact List.mem_reverse.mpr List.mem_cons_self

/-- And it is present even when it alone would blow the whole budget. -/
theorem window_keeps_newest_when_oversized (budget : Nat) (turns : List Turn)
    (t : Turn) (rest : List Turn)
    (hsrc : (turns.filter (·.substantive)).reverse = t :: rest)
    (hbig : budget < t.size) :
    ∃ kept ∈ window 1 budget turns, kept.id = t.id ∧ kept.size = budget := by
  refine ⟨{ t with size := min t.size budget }, ?_, rfl, by simp; omega⟩
  unfold window
  rw [hsrc]
  rw [List.take_succ_cons, keep]
  exact List.mem_reverse.mpr List.mem_cons_self

end ContextWindow

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms ContextWindow.window_within_budget
#print axioms ContextWindow.window_within_limit
#print axioms ContextWindow.window_all_substantive
#print axioms ContextWindow.window_keeps_newest
#print axioms ContextWindow.window_keeps_newest_when_oversized
