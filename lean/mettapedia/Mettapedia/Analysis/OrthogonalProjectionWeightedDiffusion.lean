import Mettapedia.Analysis.OrthogonalProjectionParabolic

/-!
# Weighted completion of the two projector sectors

A positive complementary-sector weight pays the transverse gradient cross
term, at an explicit inverse-weight cost on the image-sector frame gradient.
The identities retain both completed squares and the complementary frame
gradient square. No evolution law for a variable weight is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion

open OrthogonalProjectionParabolic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_sq_eq_add (P : H →L[ℝ] H) (hp : P * P = P)
    (hs : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫) (w : H) :
    ‖w‖ ^ 2 = ‖P w‖ ^ 2 + ‖(1 - P) w‖ ^ 2 := by
  have hi := hs w (P w)
  rw [apply_idempotent P hp, real_inner_self_eq_norm_sq] at hi
  change _ = _ + ‖w - P w‖ ^ 2
  rw [norm_sub_sq_real]
  linarith

theorem weighted_completed_squares (theta : ℝ) (htheta : theta ≠ 0) (c d a b : H) :
    (1 - theta) * (‖c + b‖ ^ 2 + 2 * ⟪d, a⟫ - ‖a‖ ^ 2) +
        theta * (‖c‖ ^ 2 + ‖d‖ ^ 2) =
      ‖c + (1 - theta) • b‖ ^ 2 + theta * ‖d + ((1 - theta) / theta) • a‖ ^ 2 +
        theta * (1 - theta) * ‖b‖ ^ 2 - (1 - theta) / theta * ‖a‖ ^ 2 := by
  simp only [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp
  ring

theorem weighted_signed_diffusion_split {ι : Type*} [Fintype ι]
    (P W : H →L[ℝ] H) (G : ι → H →L[ℝ] H) (nu theta : ℝ) (htheta : theta ≠ 0)
    (hp : P * P = P) (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫)
    (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫)
    (hsG : ∀ j a b, ⟪G j a, b⟫ = ⟪a, G j b⟫)
    (ht : ∀ j, G j * P + P * G j = G j)
    (hW : W * P + P * W = W + (2 * nu) • (∑ j, G j * G j)) (w : H) (v : ι → H) :
    (1 - theta) * (⟪w, W w⟫ - 2 * nu * (∑ j, ‖P (v j)‖ ^ 2) -
        4 * nu * (∑ j, ⟪v j, G j w⟫)) - 2 * nu * theta * (∑ j, ‖v j‖ ^ 2) =
      (1 - theta) * (2 * ⟪P w, W ((1 - P) w)⟫) +
        2 * nu * ((1 - theta) / theta) * (∑ j, ‖G j (P w)‖ ^ 2) -
        2 * nu * theta * (1 - theta) * (∑ j, ‖G j ((1 - P) w)‖ ^ 2) -
        2 * nu * (∑ j, ‖P (v j) + (1 - theta) • G j ((1 - P) w)‖ ^ 2) -
        2 * nu * theta * (∑ j, ‖(1 - P) (v j) + ((1 - theta) / theta) • G j (P w)‖ ^ 2) := by
  rw [signed_diffusion_split P W G nu hp hsP hsW hsG ht hW w v]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl (fun j _ ↦
    weighted_completed_squares theta htheta (P (v j)) ((1 - P) (v j)) (G j (P w)) (G j ((1 - P) w)))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hn : (∑ j, ‖v j‖ ^ 2) = (∑ j, ‖P (v j)‖ ^ 2) + (∑ j, ‖(1 - P) (v j)‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ norm_sq_eq_add P hp hsP (v j))
  rw [hn]
  linear_combination -2 * nu * h

theorem abs_weighted_cross_le_young (P W : H →L[ℝ] H) (hp : P * P = P)
    (hsP : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫) (hsW : ∀ a b, ⟪W a, b⟫ = ⟪a, W b⟫)
    (w : H) (r K rho : ℝ) (hK : ‖(1 - P) * W * P‖ ≤ K) (hrho : 0 < rho) :
    |r * (2 * ⟪P w, W ((1 - P) w)⟫)| ≤
      rho * ‖P w‖ ^ 2 + r ^ 2 * K ^ 2 / rho * ‖(1 - P) w‖ ^ 2 := by
  have hYoung : 2 * |r| * K * ‖P w‖ * ‖(1 - P) w‖ ≤
      (rho ^ 2 * ‖P w‖ ^ 2 + r ^ 2 * K ^ 2 * ‖(1 - P) w‖ ^ 2) / rho := by
    apply (le_div_iff₀ hrho).mpr
    have h := sq_nonneg (rho * ‖P w‖ - |r| * K * ‖(1 - P) w‖)
    simp only [sub_sq, mul_pow, sq_abs] at h
    nlinarith only [h]
  rw [abs_mul]
  calc
    _ ≤ |r| * (2 * ‖(1 - P) * W * P‖ * ‖P w‖ * ‖(1 - P) w‖) := by
      gcongr
      exact abs_cross_le P W hp hsP hsW w
    _ ≤ |r| * (2 * K * ‖P w‖ * ‖(1 - P) w‖) := by gcongr
    _ = 2 * |r| * K * ‖P w‖ * ‖(1 - P) w‖ := by ring
    _ ≤ _ := hYoung
    _ = _ := by field_simp

end Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion
