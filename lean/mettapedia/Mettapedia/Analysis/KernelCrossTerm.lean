import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A cross term cannot be paid by a projected gradient alone

If a fixed vector has a nonzero pairing with a direction in the kernel
of a linear map, its linear cross term is unbounded on that kernel.
Consequently no multiple of the projected squared norm, plus a fixed
constant, controls this term. This is an algebraic obstruction, not a
counterexample to an evolution equation or an integrated estimate.
-/

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace Mettapedia.Analysis.KernelCrossTerm

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_kernel_crossTerm_gt (P : H →L[ℝ] V) (z b : H)
    (hz : P z = 0) (hb : ⟪z, b⟫ ≠ 0) (M : ℝ) :
    ∃ v : H, P v = 0 ∧ M < -4 * ⟪v, b⟫ := by
  refine ⟨(-(M + 1) / (4 * ⟪z, b⟫)) • z, ?_, ?_⟩
  · rw [map_smul, hz, smul_zero]
  · rw [real_inner_smul_left]
    have he : -4 * (-(M + 1) / (4 * ⟪z, b⟫) * ⟪z, b⟫) = M + 1 := by
      field_simp
    rw [he]
    linarith

theorem not_exists_projectedSquare_bound (P : H →L[ℝ] V) (z b : H)
    (hz : P z = 0) (hb : ⟪z, b⟫ ≠ 0) :
    ¬ ∃ A B : ℝ, ∀ v : H, -4 * ⟪v, b⟫ ≤ A * ‖P v‖ ^ 2 + B := by
  rintro ⟨A, B, h⟩
  obtain ⟨v, hv, hgt⟩ := exists_kernel_crossTerm_gt P z b hz hb B
  have hvb := h v
  simp only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_add] at hvb
  exact (not_lt_of_ge hvb) hgt

end Mettapedia.Analysis.KernelCrossTerm
