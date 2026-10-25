import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Compaction and recovery from an oversized request

A coding agent's request holds fixed parts (instructions, tools), a summary of
older history, and the newer history verbatim. When the provider rejects a
request as too large, the agent must shrink it; resending it unchanged fails
again. This file compares three recovery rules and one accounting rule.

* **Fold a fraction, once.** Folding the older half of the unfolded history
  into the summary, and giving up if the shrunk request is still rejected,
  is not live: one fold can leave a request that is still too large although
  folding further would fit (`foldOnce_not_live`). A single fold bounds
  nothing: the retained half can be arbitrarily large (`fold_tail_unbounded`).
* **Fold while it helps.** Repeating the fold after each rejection, as long as
  at least two items are unfolded, terminates for every fold that folds at
  least one item and keeps the newest (`repairLoop` is well founded), and
  ends with an accepted request whenever the newest item alone fits
  (`repairLoop_live`). Every resent request is strictly smaller than the one
  before, and the newest item is never folded (`fold_keeps_newest`).
* **Retain a bounded tail.** Keeping only the newest history within a budget
  `R` bounds the request by the fixed parts, the summary and `R` whatever the
  history (`keepWithin_sum_le`), so one compaction suffices when that bound
  fits the window (`keepWithin_fits`).
* **Record a rejection as a full window.** An agent that compacts before a turn
  when its recorded usage reaches a limit must record a rejected request as
  having filled the window. Recording the window minus the cumulative usage of
  the whole session gives zero once that cumulative total reaches the window
  (`fill_zero`), and stays zero after every further rejection (`fill_fixed`),
  so the next turn does not compact and resends the oversized history
  (`fill_no_compaction`). Recording the window itself compacts at once
  (`full_window_compacts`).

The model knows sizes only; what a summary says is outside it. The provider
accepts exactly the requests that fit its window.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Agent.CodingAgent.Compaction

/-! ## Requests -/

/-- The size of a request: fixed parts `base`, a summary of size `s`, and the
history items (sizes, oldest first) from `offset` on, the folded ones being
those before `offset`. -/
def requestSize (base s : ℕ) (items : List ℕ) (offset : ℕ) : ℕ :=
  base + s + (items.drop offset).sum

/-- Dropping more of the history never enlarges what remains. -/
theorem sum_drop_antitone (items : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (items.drop b).sum ≤ (items.drop a).sum := by
  have hb : b = a + (b - a) := by omega
  rw [hb, ← List.drop_drop]
  have := List.sum_take_add_sum_drop (items.drop a) (b - a)
  omega

/-! ## Folding while it helps -/

/-- A fold rule: given `m ≥ 2` unfolded items, how many of the oldest to fold.
It folds at least one and keeps at least the newest. -/
structure FoldRule where
  step : ℕ → ℕ
  progress : ∀ m, 2 ≤ m → 1 ≤ step m
  keeps : ∀ m, 2 ≤ m → step m ≤ m - 1

/-- Folding the older half: `⌊m/2⌋` of `m` unfolded items. -/
def half : FoldRule where
  step m := m / 2
  progress m h := by omega
  keeps m h := by omega

/-- Repair after each rejection while at least two items are unfolded. The
result is the final offset and whether its request was accepted. -/
def repairLoop (rule : FoldRule) (W base s : ℕ) (items : List ℕ) (offset : ℕ) : ℕ × Bool :=
  if requestSize base s items offset ≤ W then (offset, true)
  else if _h : items.length - offset ≤ 1 then (offset, false)
  else repairLoop rule W base s items (offset + rule.step (items.length - offset))
termination_by items.length - offset
decreasing_by
  have h1 := rule.progress (items.length - offset) (by omega)
  have h2 := rule.keeps (items.length - offset) (by omega)
  omega

/-- A fold keeps the newest item unfolded. -/
theorem fold_keeps_newest (rule : FoldRule) (n offset : ℕ) (h : 2 ≤ n - offset) :
    offset + rule.step (n - offset) < n := by
  have := rule.keeps (n - offset) h
  omega

/-- **Folding while it helps is live.** If the newest item alone fits beside
the fixed parts and the summary, repeated repair from any offset before the
newest item ends with an accepted request. -/
theorem repairLoop_live (rule : FoldRule) (W base s : ℕ) (items : List ℕ)
    (hne : items ≠ []) (hfit : base + s + items.getLast hne ≤ W) :
    ∀ offset, offset < items.length → (repairLoop rule W base s items offset).2 = true := by
  suffices key : ∀ k offset, items.length - offset = k → offset < items.length →
      (repairLoop rule W base s items offset).2 = true from
    fun offset h => key _ offset rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro offset hk hlt
    rw [repairLoop]
    split
    · rfl
    · rename_i hreject
      split
      · rename_i hle
        exfalso
        apply hreject
        have hoff : offset = items.length - 1 := by omega
        simpa [requestSize, hoff, List.drop_length_sub_one hne] using hfit
      · rename_i hgt
        have h2 : 2 ≤ items.length - offset := by omega
        have hlt' := fold_keeps_newest rule items.length offset h2
        have hp := rule.progress (items.length - offset) h2
        exact ih _ (by omega) _ rfl hlt'

/-- Each repeated repair resends a request no larger than the one before. -/
theorem fold_shrinks (rule : FoldRule) (base s : ℕ) (items : List ℕ) (offset : ℕ) :
    requestSize base s items (offset + rule.step (items.length - offset)) ≤
      requestSize base s items offset := by
  unfold requestSize
  have := sum_drop_antitone items (Nat.le_add_right offset (rule.step (items.length - offset)))
  omega

/-! ## Folding a fraction once -/

/-- Fold once after a rejection, and give up if the shrunk request is still
rejected. -/
def foldOnce (rule : FoldRule) (W base s : ℕ) (items : List ℕ) : Bool :=
  decide (requestSize base s items 0 ≤ W) ||
    (decide (2 ≤ items.length) && decide (requestSize base s items (rule.step items.length) ≤ W))

/-- One fold of the older half is not enough: four items of size 10 against a
window of 15 still need 20 after one fold and give up, while repeated folding
reaches the newest item, which fits. -/
theorem foldOnce_not_live :
    foldOnce half 15 0 0 [10, 10, 10, 10] = false ∧
      (repairLoop half 15 0 0 [10, 10, 10, 10] 0).2 = true := by
  refine ⟨by decide, ?_⟩
  exact repairLoop_live half 15 0 0 [10, 10, 10, 10] (by simp) (by simp) 0 (by simp)

/-- One fold bounds nothing: the retained half can exceed any bound. -/
theorem fold_tail_unbounded (B : ℕ) :
    ∃ items : List ℕ, B < (items.drop (half.step items.length)).sum := by
  refine ⟨List.replicate (2 * B + 2) 1, ?_⟩
  simp only [half, List.length_replicate, List.drop_replicate, List.sum_replicate, smul_eq_mul,
    mul_one]
  omega

/-! ## Retaining a bounded tail -/

/-- Take items newest first while they fit the remaining budget; the first
item that does not fit is cut to what remains, and selection stops there. -/
def takeWithin : ℕ → List ℕ → List ℕ
  | _, [] => []
  | R, x :: xs => if x ≤ R then x :: takeWithin (R - x) xs else [R]

theorem takeWithin_sum_le : ∀ (R : ℕ) (l : List ℕ), (takeWithin R l).sum ≤ R
  | _, [] => by simp [takeWithin]
  | R, x :: xs => by
    unfold takeWithin
    split
    · have := takeWithin_sum_le (R - x) xs
      simp only [List.sum_cons]
      omega
    · simp

/-- The newest history within budget `R`, in its original order. -/
def keepWithin (R : ℕ) (items : List ℕ) : List ℕ := (takeWithin R items.reverse).reverse

/-- The retained tail never exceeds its budget, whatever the history. -/
theorem keepWithin_sum_le (R : ℕ) (items : List ℕ) : (keepWithin R items).sum ≤ R := by
  simpa [keepWithin, List.sum_reverse] using takeWithin_sum_le R items.reverse

/-- **One bounded compaction suffices** when the fixed parts, the summary and
the budget fit the window together. -/
theorem keepWithin_fits (W base s R : ℕ) (items : List ℕ) (h : base + s + R ≤ W) :
    base + s + (keepWithin R items).sum ≤ W := by
  have := keepWithin_sum_le R items
  omega

/-! ## Recording a rejection -/

/-- The usage record after a rejected request under the faulty rule: the
session's cumulative total becomes the window, and the last-turn usage becomes
the window minus the previous cumulative total. -/
def fillToWindow (W cumulative : ℕ) : ℕ × ℕ := (W, W - cumulative)

/-- The pre-turn check: compact when the recorded last-turn usage plus the
estimate of the items since the last reply reaches the limit. -/
def compactsBeforeTurn (limit last since : ℕ) : Bool := decide (limit ≤ last + since)

/-- Once the session's cumulative usage reaches the window, a rejection is
recorded as zero last-turn usage. -/
theorem fill_zero (W cumulative : ℕ) (h : W ≤ cumulative) :
    (fillToWindow W cumulative).2 = 0 := by
  simp [fillToWindow]
  omega

/-- A further rejection records zero again, since the cumulative total now
equals the window. -/
theorem fill_fixed (W cumulative : ℕ) :
    fillToWindow W (fillToWindow W cumulative).1 = (W, 0) := by
  simp [fillToWindow]

/-- So the next turn does not compact until the new items alone reach the
limit, and the oversized history is sent again. -/
theorem fill_no_compaction (W cumulative limit since : ℕ) (h : W ≤ cumulative)
    (hs : since < limit) :
    compactsBeforeTurn limit (fillToWindow W cumulative).2 since = false := by
  unfold compactsBeforeTurn fillToWindow
  exact decide_eq_false (by omega)

/-- Recording the window itself as the last-turn usage compacts on the next
turn. -/
theorem full_window_compacts (W limit since : ℕ) (h : limit ≤ W) :
    compactsBeforeTurn limit W since = true := by
  simp [compactsBeforeTurn]
  omega

end Mettapedia.CogArch.Agent.CodingAgent.Compaction
