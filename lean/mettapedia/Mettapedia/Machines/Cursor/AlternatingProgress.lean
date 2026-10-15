import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Progress cost for alternating ordered iterators

Two-way leapfrog navigation advances one iterator past at least one distinct
key, then rotates to the other iterator. A completed match advances past its
whole equal-key range. Binary seeks may discard additional keys. This account
records those productive advances, separately from seeks, child navigation,
leaf processing and preparation.

The native range/ordering correspondence must establish strict progress and
rotation. These laws do not bound an arbitrary intersection implementation or
replace its semantic correctness proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.AlternatingProgress

/-- A finite trace of productive advances. `true` selects the left iterator.
Exhaustion ends the trace; a step preserves the other remaining-key count. -/
inductive Execution : Bool → Nat → Nat → Nat → Prop where
  | exhausted (left right : Nat) (empty : left = 0 ∨ right = 0) (current : Bool) :
      Execution current left right 0
  | left {left right after work : Nat} (positive : 0 < right)
      (progress : after < left) (rest : Execution false after right work) :
      Execution true left right (work + 1)
  | right {left right after work : Nat} (positive : 0 < left)
      (progress : after < right) (rest : Execution true left after work) :
      Execution false left right (work + 1)

/-- Parity keeps the unmatched partial round explicit. -/
theorem directional_bounds {current : Bool} {left right work : Nat}
    (execution : Execution current left right work) :
    work ≤ 2 * left - (if current then 1 else 0) ∧
      work ≤ 2 * right - (if current then 0 else 1) := by
  induction execution with
  | exhausted left right empty current => cases current <;> simp
  | left positive progress rest ih =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ih
      simp only [↓reduceIte]
      omega
  | right positive progress rest ih =>
      simp only [↓reduceIte] at ih
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem advances_le_twice_smaller {current : Bool} {left right work : Nat}
    (execution : Execution current left right work) :
    work ≤ 2 * min left right := by
  have bounds := directional_bounds execution
  cases current <;> simp only [Bool.false_eq_true, ↓reduceIte] at bounds <;> omega

/-- A selected minimum-side iterator needs no unmatched extra advance. -/
theorem minimum_side_first {left right work : Nat}
    (execution : Execution true left right work) (smaller : left ≤ right) :
    work ≤ 2 * min left right := by
  have bounds := (directional_bounds execution).1
  simp only [↓reduceIte] at bounds
  rw [min_eq_left smaller]
  omega

/-- Both initial sizes and all discarded keys remain charged. -/
theorem advances_le_total_keys {current : Bool} {left right work : Nat}
    (execution : Execution current left right work) : work ≤ left + right := by
  induction execution with
  | exhausted left right empty current => omega
  | left positive progress rest ih => omega
  | right positive progress rest ih => omega

/-- Starting on the larger side can consume two advances for one small key. -/
theorem larger_side_first : Execution false 1 2 2 := by
  apply Execution.right (by decide) (show 1 < 2 by decide)
  apply Execution.left (by decide) (show 0 < 1 by decide)
  exact Execution.exhausted 0 1 (Or.inl rfl) false

/-- Strict progress alone does not imply the minimum-side bound. -/
inductive Unrotated : Nat → Nat → Nat → Prop where
  | exhausted (right : Nat) : Unrotated 0 right 0
  | step {left right after work : Nat} (positive : 0 < right)
      (progress : after < left) (rest : Unrotated after right work) :
      Unrotated left right (work + 1)

theorem dropping_rotation_loses_the_bound :
    Unrotated 4 1 4 ∧ 4 > 2 * min 4 1 := by
  refine ⟨?_, by decide⟩
  apply Unrotated.step (by decide) (show 3 < 4 by decide)
  apply Unrotated.step (by decide) (show 2 < 3 by decide)
  apply Unrotated.step (by decide) (show 1 < 2 by decide)
  apply Unrotated.step (by decide) (show 0 < 1 by decide)
  exact Unrotated.exhausted 1

/-- Every advance can charge a fixed local overhead plus a bounded seek cost;
child/output work is supplied separately rather than hidden in this bound. -/
theorem charged_work_bound {current : Bool} {left right advances : Nat}
    (execution : Execution current left right advances)
    (overhead seek child : Nat) :
    advances * (overhead + seek) + child ≤
      (2 * min left right) * (overhead + seek) + child := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (advances_le_twice_smaller execution)) child

end Mettapedia.Machines.Cursor.AlternatingProgress
