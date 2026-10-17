import Mettapedia.GSLT.Dynamics.PriorityFairness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounded overtaking: the fairness certificate of a priority scheduler

A least-first scheduler (`PriorityFairness.Run`) serves an item once everything
ahead of it has been served.  Work that arrives ahead of the item overtakes it.
Strict priority places no bound on overtaking, and an item can starve
(`PriorityFairness.Controls.priority_not_weakly_fair`).

* **Bounded overtaking bounds waiting** (`fires_within_overtaking`): if at most
  `B` items arrive ahead of `x` from time `start` on, `x` fires within
  `|ahead| + B` steps of `start`.  `PriorityFairness.Run.fires_within` is the
  case `B = 0`.  The bound `B` is the per-item fairness certificate; a
  progress certificate that only guarantees recurrence of stable states does
  not provide it.
* **Deadlines are aging** (`deadline_fires_within`): key each item first by a
  deadline stamped at arrival later than the arrival time, for example arrival
  time plus a slack chosen by priority.  If at most `k` items arrive per step,
  an item with deadline `d` fires within `|ahead| + k d` steps.  Urgent work gets
  a small slack and is served first among items due at the same time, and no
  stream of urgent work starves an older item.  Epochs are the case of
  deadlines rounded to a period.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PriorityFairness

universe u

namespace Run

variable {α : Type u} [LinearOrder α] (run : Run α)

/-- The arrivals at time `t` that land ahead of `x`. -/
def overtakers (t : ℕ) (x : α) : Finset α := (run.arrivals t).filter (· < x)

/-- One step without serving `x`: the item served was ahead of `x`, and only
overtakers join those ahead. -/
theorem ahead_card_step {t : ℕ} {x : α} (pending : x ∈ run.pending t) (notFired : run.fired t ≠ x) :
    x ∈ run.pending (t + 1) ∧
      (run.ahead (t + 1) x).card + 1 ≤ (run.ahead t x).card + (run.overtakers t x).card := by
  have firedAhead : run.fired t ∈ run.ahead t x :=
    Finset.mem_filter.2 ⟨run.fired_mem t,
      lt_of_le_of_ne (run.fired_least t x pending) notFired⟩
  constructor
  · rw [run.next t]
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨notFired.symm, pending⟩)
  · have sub : run.ahead (t + 1) x ⊆ (run.ahead t x).erase (run.fired t) ∪ run.overtakers t x := by
      intro y member
      obtain ⟨inNext, below⟩ := Finset.mem_filter.1 member
      rw [run.next t] at inNext
      rcases Finset.mem_union.1 inNext with erased | arrived
      · obtain ⟨ne, inPending⟩ := Finset.mem_erase.1 erased
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨ne, Finset.mem_filter.2 ⟨inPending, below⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨arrived, below⟩)
    have := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem firedAhead] at this
    have pos : 0 < (run.ahead t x).card := Finset.card_pos.2 ⟨_, firedAhead⟩
    omega

/-- **Bounded overtaking bounds waiting.** -/
theorem fires_within_overtaking {start : ℕ} {x : α} (pending : x ∈ run.pending start) (B : ℕ)
    (budget : ∀ k, ∑ s ∈ Finset.range k, (run.overtakers (start + s) x).card ≤ B) :
    ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card + B ∧ run.fired t = x := by
  by_contra never
  simp only [not_exists, not_and] at never
  have claim : ∀ k, k ≤ (run.ahead start x).card + B + 1 →
      x ∈ run.pending (start + k) ∧
        (run.ahead (start + k) x).card + k ≤
          (run.ahead start x).card + ∑ s ∈ Finset.range k, (run.overtakers (start + s) x).card := by
    intro k
    induction k with
    | zero => intro _; simpa using pending
    | succ k ih =>
        intro le
        obtain ⟨member, count⟩ := ih (by omega)
        have notFired : run.fired (start + k) ≠ x :=
          never (start + k) (Nat.le_add_right _ _) (by omega)
        obtain ⟨member', step⟩ := run.ahead_card_step member notFired
        refine ⟨member', ?_⟩
        rw [Finset.sum_range_succ, ← Nat.add_assoc start k 1]
        omega
  obtain ⟨_, count⟩ := claim ((run.ahead start x).card + B + 1) le_rfl
  have := budget ((run.ahead start x).card + B + 1)
  omega

end Run

/-! ## Deadlines -/

section Deadlines

variable {Key : Type u} [LinearOrder Key]

/-- **Deadlines are aging**: with deadlines stamped later than arrival and at
most `k` arrivals per step, an item with deadline `d` fires within
`|ahead| + k d` steps. -/
theorem deadline_fires_within (run : Run (Lex (ℕ × Key))) {start : ℕ} {x : Lex (ℕ × Key)}
    (pending : x ∈ run.pending start) (k : ℕ) (rate : ∀ t, (run.arrivals t).card ≤ k)
    (stamped : ∀ t, ∀ y ∈ run.arrivals t, t < (ofLex y).1) :
    ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card + k * (ofLex x).1 ∧ run.fired t = x := by
  refine run.fires_within_overtaking pending (k * (ofLex x).1) fun K => ?_
  have term : ∀ s ∈ Finset.range K, (run.overtakers (start + s) x).card ≤
      if start + s < (ofLex x).1 then k else 0 := by
    intro s _
    split_ifs with due
    · exact (Finset.card_filter_le _ _).trans (rate _)
    · apply le_of_eq
      rw [Finset.card_eq_zero, Run.overtakers, Finset.filter_eq_empty_iff]
      intro y arrived ahead
      have late := stamped _ y arrived
      have : (ofLex y).1 ≤ (ofLex x).1 := by
        rcases Prod.Lex.lt_iff.1 ahead with lt | ⟨eq, _⟩
        · exact lt.le
        · exact eq.le
      omega
  calc ∑ s ∈ Finset.range K, (run.overtakers (start + s) x).card
      ≤ ∑ s ∈ Finset.range K, if start + s < (ofLex x).1 then k else 0 := Finset.sum_le_sum term
    _ = ((Finset.range K).filter fun s => start + s < (ofLex x).1).card * k := by
        rw [← Finset.sum_filter]
        simp
    _ ≤ (ofLex x).1 * k := by
        apply Nat.mul_le_mul_right
        calc ((Finset.range K).filter fun s => start + s < (ofLex x).1).card
            ≤ (Finset.range (ofLex x).1).card := by
              apply Finset.card_le_card
              intro s member
              simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
              omega
          _ = (ofLex x).1 := Finset.card_range _
    _ = k * (ofLex x).1 := mul_comm _ _

end Deadlines

end Mettapedia.GSLT.Dynamics.PriorityFairness
