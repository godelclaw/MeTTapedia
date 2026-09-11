import Mettapedia.Analysis.CompactRangeCover
import Mathlib.Analysis.Normed.Group.Real

/-! Discontinuous fields, empty sources, and the necessity of a common range bound. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis.CompactRangeCover

/-- Even a discontinuous two-state field has an adaptive cover of bounded size. -/
example : ∃ M : ℕ, 0 < M ∧ ∃ centers : Finset ℝ, centers.card ≤ M ∧
    ∀ x : ℝ, ∃ y ∈ centers,
      ‖(if x ≤ 0 then (1 : ℝ) else -1) - (if y ≤ 0 then (1 : ℝ) else -1)‖ < 1 / 4 := by
  obtain ⟨M, hM, h⟩ := exists_uniform_card_norm_cover (X := ℝ) (E := ℝ) 1 (1 / 4) (by norm_num)
  refine ⟨M, hM, h (fun x ↦ if x ≤ 0 then 1 else -1) ?_⟩
  intro x
  split_ifs <;> norm_num

example : ∃ M : ℕ, 0 < M ∧ ∃ centers : Finset (Fin 0), centers.card ≤ M ∧ centers = ∅ := by
  obtain ⟨M, hM, h⟩ := exists_uniform_card_norm_cover (X := Fin 0) (E := ℝ) (-1) 1 (by norm_num)
  obtain ⟨centers, hc, _⟩ := h (fun _ ↦ 0) (fun i ↦ Fin.elim0 i)
  exact ⟨M, hM, centers, hc, Finset.eq_empty_of_isEmpty centers⟩

/-- The uniform bound precedes an arbitrary sequence of bounded values. -/
example : ∃ M : ℕ, 0 < M ∧ ∀ a : ℕ → ℝ, (∀ n, ‖a n‖ ≤ 7) →
    ∃ centers : Finset ℕ, centers.card ≤ M ∧ ∀ n, ∃ k ∈ centers, ‖a n - a k‖ < 1 :=
  exists_uniform_card_norm_cover 7 1 (by norm_num)

/-- Dropping range control would be false: separated unbounded values admit no finite cover. -/
example : ¬ ∃ centers : Finset ℕ, ∀ n : ℕ, ∃ k ∈ centers, ‖(n : ℝ) - k‖ < 1 / 2 := by
  rintro ⟨centers, h⟩
  obtain ⟨k, hk, hclose⟩ := h ((∑ i ∈ centers, i) + 1)
  have hk' : k ≤ ∑ i ∈ centers, i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hk
  have hcast : (k : ℝ) + 1 ≤ ((∑ i ∈ centers, i) + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hk' 1
  rw [Real.norm_eq_abs] at hclose
  have hlt := lt_of_le_of_lt (le_abs_self (((∑ i ∈ centers, i) + 1 : ℕ) - (k : ℝ))) hclose
  linarith

#print axioms exists_uniform_card_cover
#print axioms exists_uniform_card_norm_cover
