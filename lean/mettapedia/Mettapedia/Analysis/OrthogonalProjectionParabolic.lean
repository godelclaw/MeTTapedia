import Mettapedia.Analysis.IdempotentDerivatives
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Signed sector decomposition for a parabolic orthogonal projector

The complementary-gradient cross term is separated from a favorable
completed square. This uses the quadratic defect of the parabolic rate,
not a first-order tangent identity for that rate.
-/

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace Mettapedia.Analysis.OrthogonalProjectionParabolic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem apply_idempotent (P : H →L[ℝ] H) (hp : P * P = P) (w : H) : P (P w) = P w :=
  congrArg (fun A : H →L[ℝ] H ↦ A w) hp

theorem apply_complement (P : H →L[ℝ] H) (hp : P * P = P) (w : H) : P ((1 - P) w) = 0 := by
  simp only [sub_apply, one_apply_eq_self, map_sub, apply_idempotent P hp, sub_self]

theorem tangent_image_zero (P G : H →L[ℝ] H) (hp : P * P = P)
    (ht : G * P + P * G = G) (w : H) : P (G (P w)) = 0 := by
  have h := congrArg (fun A : H →L[ℝ] H ↦ A (P w)) ht
  change G (P (P w)) + P (G (P w)) = G (P w) at h
  rw [apply_idempotent P hp] at h
  exact add_eq_left.mp h

theorem tangent_complement_eq (P G : H →L[ℝ] H)
    (ht : G * P + P * G = G) (w : H) : G ((1 - P) w) = P (G w) := by
  have h := congrArg (fun A : H →L[ℝ] H ↦ A w) ht
  change G (P w) + P (G w) = G w at h
  simp only [sub_apply, one_apply_eq_self, map_sub]
  linear_combination (norm := abel) -h

theorem tangent_cross_split (P G : H →L[ℝ] H) (hp : P * P = P)
    (hs : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫) (ht : G * P + P * G = G) (v w : H) :
    ⟪v, G w⟫ = ⟪P v, G ((1 - P) w)⟫ + ⟪(1 - P) v, G (P w)⟫ := by
  have hz : ⟪P v, G (P w)⟫ = 0 := by
    rw [hs, tangent_image_zero P G hp ht w, inner_zero_right]
  have he := congrArg (fun A : H →L[ℝ] H ↦ ⟪v, A w⟫) ht
  simp only [add_apply, mul_apply_eq_comp, inner_add_right, ← hs v (G w)] at he
  simp only [sub_apply, one_apply_eq_self, map_sub, inner_sub_left, inner_sub_right, hz]
  linarith

theorem quadratic_split (P W : H →L[ℝ] H)
    (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫) (w : H) :
    ⟪w, W w⟫ = ⟪P w, W (P w)⟫ + 2 * ⟪P w, W ((1 - P) w)⟫ +
      ⟪(1 - P) w, W ((1 - P) w)⟫ := by
  have hs : ⟪w, W (P w)⟫ = ⟪P w, W w⟫ := by rw [← hsW, real_inner_comm]
  simp only [sub_apply, one_apply_eq_self, map_sub, inner_sub_left, inner_sub_right, hs]
  ring

theorem quadratic_sum_squares {ι : Type*} [Fintype ι] (G : ι → H →L[ℝ] H)
    (hs : ∀ j a b, ⟪G j a, b⟫ = ⟪a, G j b⟫) (w : H) :
    ⟪w, (∑ j, G j * G j) w⟫ = ∑ j, ‖G j w‖ ^ 2 := by
  simp only [sum_apply, inner_sum, mul_apply_eq_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hs j w (G j w), real_inner_self_eq_norm_sq]

theorem complement_symmetric (P : H →L[ℝ] H)
    (hs : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫) :
    ∀ a b, ⟪(1 - P) a, b⟫ = ⟪a, (1 - P) b⟫ := by
  intro a b
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hs]

theorem quadratic_image_defect {ι : Type*} [Fintype ι]
    (P W : H →L[ℝ] H) (G : ι → H →L[ℝ] H) (c : ℝ)
    (hp : P * P = P) (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsG : ∀ j a b, ⟪G j a, b⟫ = ⟪a, G j b⟫)
    (hW : W * P + P * W = W + c • (∑ j, G j * G j)) (w : H) :
    ⟪P w, W (P w)⟫ = c * ∑ j, ‖G j (P w)‖ ^ 2 := by
  have h := congrArg (fun A : H →L[ℝ] H ↦ ⟪w, A w⟫)
    (idempotent_defect_image_block P W _ hp hW)
  simp only [mul_apply_eq_comp, smul_apply, map_smul, real_inner_smul_right] at h
  rw [← hsP, ← hsP, quadratic_sum_squares G hsG] at h
  exact h

theorem quadratic_complement_defect {ι : Type*} [Fintype ι]
    (P W : H →L[ℝ] H) (G : ι → H →L[ℝ] H) (c : ℝ)
    (hp : P * P = P) (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsG : ∀ j a b, ⟪G j a, b⟫ = ⟪a, G j b⟫)
    (hW : W * P + P * W = W + c • (∑ j, G j * G j)) (w : H) :
    ⟪(1 - P) w, W ((1 - P) w)⟫ = -c * ∑ j, ‖G j ((1 - P) w)‖ ^ 2 := by
  have hsQ := complement_symmetric P hsP
  have h := congrArg (fun A : H →L[ℝ] H ↦ ⟪w, A w⟫)
    (idempotent_defect_complement_block P W _ hp hW)
  simp only [mul_apply_eq_comp, smul_apply, neg_apply, map_smul,
    real_inner_smul_right, inner_neg_right] at h
  rw [← hsQ, ← hsQ, quadratic_sum_squares G hsG] at h
  simpa only [neg_mul, mul_neg] using h

theorem gradient_completed_square (P G : H →L[ℝ] H) (hp : P * P = P)
    (hs : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫) (ht : G * P + P * G = G)
    (nu : ℝ) (v w : H) :
    -2 * nu * ‖P v‖ ^ 2 - 4 * nu * ⟪v, G w⟫ - 2 * nu * ‖G ((1 - P) w)‖ ^ 2 =
      -4 * nu * ⟪(1 - P) v, G (P w)⟫ - 2 * nu * ‖P v + G ((1 - P) w)‖ ^ 2 := by
  rw [tangent_cross_split P G hp hs ht v w, norm_add_sq_real]
  ring

theorem signed_diffusion_split {ι : Type*} [Fintype ι]
    (P W : H →L[ℝ] H) (G : ι → H →L[ℝ] H) (nu : ℝ)
    (hp : P * P = P) (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫)
    (hsG : ∀ j a b, ⟪G j a, b⟫ = ⟪a, G j b⟫)
    (ht : ∀ j, G j * P + P * G j = G j)
    (hW : W * P + P * W = W + (2 * nu) • (∑ j, G j * G j)) (w : H) (v : ι → H) :
    ⟪w, W w⟫ - 2 * nu * (∑ j, ‖P (v j)‖ ^ 2) - 4 * nu * (∑ j, ⟪v j, G j w⟫) =
      2 * ⟪P w, W ((1 - P) w)⟫ + 2 * nu * (∑ j, ‖G j (P w)‖ ^ 2) -
        4 * nu * (∑ j, ⟪(1 - P) (v j), G j (P w)⟫) -
        2 * nu * (∑ j, ‖P (v j) + G j ((1 - P) w)‖ ^ 2) := by
  rw [quadratic_split P W hsW w, quadratic_image_defect P W G _ hp hsP hsG hW,
    quadratic_complement_defect P W G _ hp hsP hsG hW]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl
    (fun j _ ↦ gradient_completed_square P (G j) hp hsP (ht j) nu (v j) w)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  linarith

theorem abs_cross_le (P W : H →L[ℝ] H) (hp : P * P = P)
    (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫) (w : H) :
    |2 * ⟪P w, W ((1 - P) w)⟫| ≤ 2 * ‖(1 - P) * W * P‖ * ‖P w‖ * ‖(1 - P) w‖ := by
  have hz : ⟪(1 - P) w, P (W (P w))⟫ = 0 := by
    rw [← hsP, apply_complement P hp w, inner_zero_left]
  have he : ⟪(1 - P) w, ((1 - P) * W * P) (P w)⟫ = ⟪P w, W ((1 - P) w)⟫ := by
    simp only [mul_apply_eq_comp, apply_idempotent P hp]
    change ⟪(1 - P) w, W (P w) - P (W (P w))⟫ = _
    rw [inner_sub_right, hz, sub_zero, ← hsW, real_inner_comm]
  rw [← he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (‖(1 - P) w‖ * ‖((1 - P) * W * P) (P w)‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ 2 * (‖(1 - P) w‖ * (‖(1 - P) * W * P‖ * ‖P w‖)) := by
      gcongr
      exact ((1 - P) * W * P).le_opNorm _
    _ = _ := by ring

theorem abs_cross_le_young (P W : H →L[ℝ] H) (hp : P * P = P)
    (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫) (w : H) (K rho : ℝ)
    (hK : ‖(1 - P) * W * P‖ ≤ K) (hrho : 0 < rho) :
    |2 * ⟪P w, W ((1 - P) w)⟫| ≤ rho * ‖P w‖ ^ 2 + K ^ 2 / rho * ‖(1 - P) w‖ ^ 2 := by
  have hYoung : 2 * K * ‖P w‖ * ‖(1 - P) w‖ ≤
      (rho ^ 2 * ‖P w‖ ^ 2 + K ^ 2 * ‖(1 - P) w‖ ^ 2) / rho := by
    apply (le_div_iff₀ hrho).mpr
    nlinarith [sq_nonneg (rho * ‖P w‖ - K * ‖(1 - P) w‖)]
  calc
    _ ≤ 2 * ‖(1 - P) * W * P‖ * ‖P w‖ * ‖(1 - P) w‖ := abs_cross_le P W hp hsP hsW w
    _ ≤ 2 * K * ‖P w‖ * ‖(1 - P) w‖ := by gcongr
    _ ≤ _ := hYoung
    _ = _ := by field_simp

end Mettapedia.Analysis.OrthogonalProjectionParabolic
