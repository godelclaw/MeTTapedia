import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bellman payment for the gradient of the original passive parent

For a bounded passive vector `H`, the potential
`θ (M² - ‖H‖²) / (4 M²)` pays `θν ‖∇H‖² / (4 M²)` with sampling
penalty `θ ‖γ‖² / (4ν)`. These declarations certify its range and the
complete pointwise squares, treating each spatial derivative as a vector.
The passive PDE construction, comparison and stochastic integration are
analytic in the companion lab. Sampling controls do not force the fluid.
-/

set_option autoImplicit false
noncomputable section

namespace MettapediaNS.PassiveParentBellman

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def potential (θ M : ℝ) (H : E) : ℝ := θ * (M ^ 2 - ‖H‖ ^ 2) / (4 * M ^ 2)

omit [InnerProductSpace ℝ E] in
theorem potential_bounds (θ M : ℝ) (H : E) (hθ : 0 ≤ θ) (hM : 0 < M)
    (hH : ‖H‖ ≤ M) : 0 ≤ potential θ M H ∧ potential θ M H ≤ θ / 4 := by
  have hsq : ‖H‖ ^ 2 ≤ M ^ 2 := (sq_le_sq₀ (norm_nonneg H) hM.le).mpr hH
  constructor
  · exact div_nonneg (mul_nonneg hθ (sub_nonneg.mpr hsq)) (by positivity)
  · unfold potential
    apply (div_le_iff₀ (by positivity : 0 < 4 * M ^ 2)).mpr
    nlinarith [mul_nonneg hθ (sq_nonneg ‖H‖)]

/-- One spatial component of the full controlled production. The
second square coefficient retains the original magnitude bound. -/
theorem control_square (ν θ M β : ℝ) (H G : E) (hν : ν ≠ 0) (hM : M ≠ 0) :
    θ * ν / (2 * M ^ 2) * ‖G‖ ^ 2 + θ * β / (2 * M ^ 2) * ⟪H, G⟫ +
        θ * β ^ 2 / (4 * ν) - θ * ν / (4 * M ^ 2) * ‖G‖ ^ 2 =
      θ * ν / (4 * M ^ 2) * ‖G + (β / ν) • H‖ ^ 2 +
        θ * β ^ 2 / (4 * ν) * (1 - ‖H‖ ^ 2 / M ^ 2) := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm G H]
  field_simp
  ring

theorem controlled_gradient_paid (ν θ M β : ℝ) (H G : E)
    (hν : 0 < ν) (hθ : 0 ≤ θ) (hM : 0 < M) (hH : ‖H‖ ≤ M) :
    θ * ν / (4 * M ^ 2) * ‖G‖ ^ 2 ≤
      θ * ν / (2 * M ^ 2) * ‖G‖ ^ 2 + θ * β / (2 * M ^ 2) * ⟪H, G⟫ +
        θ * β ^ 2 / (4 * ν) := by
  have hsq : ‖H‖ ^ 2 ≤ M ^ 2 := (sq_le_sq₀ (norm_nonneg H) hM.le).mpr hH
  have hr : 0 ≤ 1 - ‖H‖ ^ 2 / M ^ 2 := by
    have : ‖H‖ ^ 2 / M ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
    linarith
  have hid := control_square ν θ M β H G hν.ne' hM.ne'
  have h₁ : 0 ≤ θ * ν / (4 * M ^ 2) * ‖G + (β / ν) • H‖ ^ 2 := by positivity
  have h₂ : 0 ≤ θ * β ^ 2 / (4 * ν) * (1 - ‖H‖ ^ 2 / M ^ 2) :=
    mul_nonneg (by positivity) hr
  linarith

/-- Conversion of the paid squared derivative to a linear observation;
the constant uses only the original magnitude bound and chosen cost share. -/
theorem linear_reward_le (ν θ M c y : ℝ) (hν : 0 < ν) (hθ : 0 < θ) (hM : 0 < M) :
    c * y ≤ θ * ν / (4 * M ^ 2) * y ^ 2 + c ^ 2 * M ^ 2 / (θ * ν) := by
  have hid : θ * ν / (4 * M ^ 2) * y ^ 2 + c ^ 2 * M ^ 2 / (θ * ν) - c * y =
      (θ * ν * y - 2 * c * M ^ 2) ^ 2 / (4 * M ^ 2 * θ * ν) := by
    field_simp
    ring
  have hnonneg : 0 ≤ (θ * ν * y - 2 * c * M ^ 2) ^ 2 / (4 * M ^ 2 * θ * ν) := by
    positivity
  linarith

end MettapediaNS.PassiveParentBellman
