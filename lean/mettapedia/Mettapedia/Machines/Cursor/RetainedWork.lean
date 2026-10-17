import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic

/-!
# Retained work: prefixes, residuals, routes and observers

A retained computation is held by handle.  Its answers, in the order its route
produces them, split into the prefix delivered so far and the residual.  This
file states the laws the native work forms keep:

* Taking prefixes neither loses nor repeats an answer: successive takes deliver
  the computation's answers in order, each once (`takes_deliver_whole`), and a
  take of `k₁` followed by a take of `k₂` delivers what one take of `k₁ + k₂`
  delivers (`take_take`).  This is the exact chunking law of the cursor
  protocol (`Protocol.resume`) read on an answer stream: the residual is
  continued, never restarted.
* A route switch at a boundary hands the residual to another route, which may
  order it differently.  The answers after the switch are a permutation of the
  residual, so the whole computation keeps its bag (`switch_keeps_bag`), while
  its order need not survive (`switch_may_reorder`).  Restarting on another
  route instead would deliver the prefix twice (`restart_repeats_prefix`).
  This is the bag observation of the relational transfer law
  (`RelationalTransfer.switching_bisimulation`).
* Observers: the count of the residual is its length (`count_take`), and over
  the factors of an independent product it is the product of the factors'
  counts, read from `n + m` stored answers (`count_product`).  An existence
  check takes the next answer and keeps it: the next take delivers it first
  (`peek_then_take`).
* Retention: cancelling releases the residual and keeps what was delivered
  (`cancel_keeps_delivered`); a reader pinned to the rows its match captured
  keeps them while the space is edited (`pinned_reader_keeps_rows`).

The model is the observation, not the machines: the native routes realize it
by the general machine's continued state, the hub's owned continuations, the
relational count cursor and the logical-update view of pinned matches.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.RetainedWork

variable {α β : Type}

/-- A retained computation: what has been delivered, and the residual, in the
order its current route produces it. -/
structure Work (α : Type) where
  delivered : List α
  residual : List α

/-- A computation not yet advanced. -/
def Work.start (answers : List α) : Work α := ⟨[], answers⟩

/-- Everything the computation gives: the delivered prefix, then the residual. -/
def Work.whole (w : Work α) : List α := w.delivered ++ w.residual

/-- A take of `k` answers: the prefix it delivers, and the work after it. -/
def Work.take (k : ℕ) (w : Work α) : List α × Work α :=
  (w.residual.take k, ⟨w.delivered ++ w.residual.take k, w.residual.drop k⟩)

/-- A take keeps the whole computation: what it delivers is removed from the
residual and appended to the delivered prefix. -/
theorem take_whole (k : ℕ) (w : Work α) : (w.take k).2.whole = w.whole := by
  simp [Work.take, Work.whole, List.append_assoc, List.take_append_drop]

/-- Two takes deliver what one take of their sum delivers. -/
theorem take_take (k₁ k₂ : ℕ) (w : Work α) :
    (w.take k₁).1 ++ ((w.take k₁).2.take k₂).1 = (w.take (k₁ + k₂)).1 := by
  simp [Work.take, List.take_add]

/-- The work after two takes is the work after one take of their sum. -/
theorem take_take_work (k₁ k₂ : ℕ) (w : Work α) :
    ((w.take k₁).2.take k₂).2 = (w.take (k₁ + k₂)).2 := by
  simp [Work.take, List.take_add, List.drop_drop, List.append_assoc]

/-- Takes until the residual is empty deliver the computation's answers in
order, each once: the delivered prefix is the whole computation. -/
theorem takes_deliver_whole (answers : List α) (k : ℕ)
    (h : answers.length ≤ k) :
    ((Work.start answers).take k).2.delivered = answers ∧
      ((Work.start answers).take k).2.residual = [] := by
  constructor
  · simp [Work.start, Work.take, List.take_of_length_le h]
  · simp [Work.start, Work.take, List.drop_eq_nil_of_le h]

/-- A take of nothing advances nothing. -/
@[simp] theorem take_zero (w : Work α) : w.take 0 = ([], w) := by
  cases w
  simp [Work.take]

/-! ## Routes -/

/-- A route switch at a boundary: the residual continues on another route,
which produces the same answers in an order of its own. -/
def Work.switch (w : Work α) (rest : List α) (_h : rest.Perm w.residual) :
    Work α :=
  ⟨w.delivered, rest⟩

/-- The whole computation keeps its bag across a switch. -/
theorem switch_keeps_bag (w : Work α) (rest : List α) (h : rest.Perm w.residual) :
    (w.switch rest h).whole.Perm w.whole := by
  simpa [Work.switch, Work.whole] using h.append_left w.delivered

/-- The delivered prefix is never taken back by a switch. -/
theorem switch_keeps_delivered (w : Work α) (rest : List α)
    (h : rest.Perm w.residual) : (w.switch rest h).delivered = w.delivered := rfl

/-- A switch need not keep the order of the residual: the hub may schedule
the remaining answers otherwise than depth first. -/
theorem switch_may_reorder :
    ∃ (w : Work ℕ) (rest : List ℕ) (h : rest.Perm w.residual),
      (w.switch rest h).whole ≠ w.whole :=
  ⟨⟨[0], [1, 2]⟩, [2, 1], List.Perm.swap 1 2 [], by decide⟩

/-- Restarting the computation on another route, instead of continuing its
residual, delivers the prefix twice: the result is not the computation's bag. -/
theorem restart_repeats_prefix (answers : List α) (k : ℕ)
    (hk : 0 < k) (hlen : 0 < answers.length) :
    ¬ (((Work.start answers).take k).1 ++ answers).Perm answers := by
  intro h
  have hl := h.length_eq
  rw [List.length_append] at hl
  have hprefix : ((Work.start answers).take k).1.length =
      min k answers.length := by
    simp [Work.start, Work.take, List.length_take]
  rw [hprefix] at hl
  have : 0 < min k answers.length := lt_min hk hlen
  omega

/-! ## Observers -/

/-- The count of the residual, as a take of all of it counts it. -/
def Work.count (w : Work α) : ℕ := w.residual.length

/-- Counting after a take counts what is left. -/
theorem count_take (k : ℕ) (w : Work α) :
    (w.take k).2.count = w.count - k := by
  simp [Work.take, Work.count, List.length_drop]

/-- A count over factors: the joint rows of two independent factors number the
product of their counts, read from `n + m` stored answers rather than the
`n · m` the enumeration would produce. -/
theorem count_product (left : List α) (right : List β) :
    (Work.start (left ×ˢ right)).count = left.length * right.length := by
  simp [Work.start, Work.count, List.length_product]

/-- An existence check that takes the next answer and keeps it for the next
take: the answer it found, and the work, in which the residual still begins
with that answer. -/
def Work.peek (w : Work α) : Option α × Work α := (w.residual.head?, w)

/-- The next take delivers the answer the existence check found, first. -/
theorem peek_then_take (w : Work α) (k : ℕ) (a : α)
    (h : (w.peek).1 = some a) (hk : 0 < k) :
    ((w.peek).2.take k).1.head? = some a := by
  obtain ⟨delivered, residual⟩ := w
  cases residual with
  | nil => simp [Work.peek] at h
  | cons x xs =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [Work.peek] at h
      simp [Work.peek, Work.take, h]

/-- An existence check is a count that stops at its first answer. -/
theorem peek_isSome_iff (w : Work α) : (w.peek).1.isSome ↔ 0 < w.count := by
  obtain ⟨delivered, residual⟩ := w
  cases residual <;> simp [Work.peek, Work.count]

/-! ## Retention -/

/-- Cancelling releases the residual; what was delivered stays delivered. -/
def Work.cancel (w : Work α) : Work α := ⟨w.delivered, []⟩

theorem cancel_keeps_delivered (w : Work α) :
    (w.cancel).delivered = w.delivered ∧ (w.cancel).residual = [] := ⟨rfl, rfl⟩

/-- A cancelled work delivers nothing more. -/
theorem cancel_take (w : Work α) (k : ℕ) : ((w.cancel).take k).1 = [] := by
  simp [Work.cancel, Work.take]

/-- A match pinned to the rows it captured: its answers are those rows' answers. -/
def pinnedMatch (rows : List β) (answer : β → Option α) : Work α :=
  Work.start (rows.filterMap answer)

/-- Edits to the space after the pin leave the pinned reader's answers to the
captured rows; a reader started after the edits reads the edited rows. -/
theorem pinned_reader_keeps_rows (captured edited : List β)
    (answer : β → Option α) (k : ℕ) :
    (((pinnedMatch captured answer).take k).2).whole =
        captured.filterMap answer ∧
      (pinnedMatch edited answer).whole = edited.filterMap answer := by
  constructor
  · rw [take_whole]
    simp [pinnedMatch, Work.start, Work.whole]
  · simp [pinnedMatch, Work.start, Work.whole]

/-- A negative example: a reader that re-read the space after an edit would see
an answer the pinned reader does not. -/
theorem reread_differs :
    ∃ (captured edited : List ℕ),
      (pinnedMatch captured some).whole ≠ (pinnedMatch edited some).whole :=
  ⟨[1, 2], [1, 2, 99], by decide⟩

end Mettapedia.Machines.Cursor.RetainedWork
