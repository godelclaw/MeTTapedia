import Mettapedia.Analysis.PeriodicRadialCorrelationDiffusion

/-!
# Exact energy of the quartic radial tensor

The polynomial tensor `|a|² a ⊗ a` has squared size `|a|⁸`.
Its derivative controls the sixth-power-weighted gradient with no loss
depending on the number of tensor entries. This is a polynomial identity,
including at zeros of the vector field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.QuarticTensorEnergy

open scoped RealInnerProductSpace
open PeriodicRadialRiesz
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem sum_quarticTensorEntry_sq (a : Rd) : (∑ i, ∑ j, quarticTensorEntry a i j ^ 2) = ‖a‖ ^ 8 := by
  simp only [quarticTensorEntry, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul,
    ← EuclideanSpace.real_norm_sq_eq]
  ring

theorem sum_mul_add_sq (a v : Rd) (c e : ℝ) :
    (∑ i, (c * a i + e * v i) ^ 2) =
      c ^ 2 * ‖a‖ ^ 2 + e ^ 2 * ‖v‖ ^ 2 + 2 * c * e * ⟪a, v⟫ := by
  calc
    _ = ‖c • a + e • v‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
    _ = _ := by
      simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_left, real_inner_smul_right]
      ring

theorem sum_quarticTensorRate_sq (a v : Rd) :
    (∑ i, ∑ j, quarticTensorRate a v i j ^ 2) =
      2 * ‖a‖ ^ 6 * ‖v‖ ^ 2 + 14 * ‖a‖ ^ 4 * ⟪a, v⟫ ^ 2 := by
  let α : Rd := (2 * ⟪a, v⟫) • a + ‖a‖ ^ 2 • v
  let β : Rd := ‖a‖ ^ 2 • a
  have he (i j : Fin d) : quarticTensorRate a v i j = α i * a j + β i * v j := by
    simp only [quarticTensorRate, α, β, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hm : (∑ i, α i * β i) = ⟪α, β⟫ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  simp_rw [he, sum_mul_add_sq]
  calc
    _ = (∑ i, α i ^ 2) * ‖a‖ ^ 2 + (∑ i, β i ^ 2) * ‖v‖ ^ 2 +
        (2 * ⟪a, v⟫) * ∑ i, α i * β i := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 2
      funext i
      ring
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq, hm]
      simp only [α, β, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_left, real_inner_smul_right, inner_add_left,
        real_inner_self_eq_norm_sq, real_inner_comm v a]
      ring

theorem weightedGradient_le (a v : Rd) :
    2 * ‖a‖ ^ 6 * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, quarticTensorRate a v i j ^ 2 := by
  rw [sum_quarticTensorRate_sq]
  exact le_add_of_nonneg_right (by positivity)

end Mettapedia.Analysis.QuarticTensorEnergy
