import Mettapedia.Analysis.RadialPower

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis.RadialPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example (a : E) : radialPower 0 a = a := by simp [radialPower]

example : radialPower 3 (0 : E) = 0 := by simp [radialPower]

example (n : ℕ) (a : E) :
    ‖radialPower n a - radialPower n (-a)‖ ^ 2 =
      ‖a‖ ^ n * ‖-a‖ ^ n * ‖a - -a‖ ^ 2 := by
  have h := norm_sub_sq_identity n a (-a)
  simp only [norm_neg, sub_self, zero_mul] at h
  simp only [norm_neg]
  linarith only [h]

example : ‖radialPower 3 (2 : ℝ) - radialPower 3 (1 : ℝ)‖ ^ 2 -
    ‖(2 : ℝ)‖ ^ 3 * ‖(1 : ℝ)‖ ^ 3 * ‖(2 : ℝ) - 1‖ ^ 2 = 217 := by
  norm_num [radialPower, norm_sub_sq_identity]

example (a b : E) :
    ‖a‖ ^ 3 * ‖b‖ ^ 3 * ‖a - b‖ ^ 2 ≤ ‖radialPower 3 a - radialPower 3 b‖ ^ 2 :=
  product_weighted_norm_sub_sq_le 3 a b

example : HasFDerivAt (radialPower 3 : E → E) (0 : E →L[ℝ] E) 0 :=
  hasFDerivAt_radialPower_three_zero

example {w : ℝ → E} {v z : E} {t : ℝ} (hw : HasDerivAt w v t)
    (hz : HasDerivAt (fun s ↦ radialPower 3 (w s)) z t) (hzero : w t = 0) : z = 0 := by
  have h := norm_derivative_radialPower_three_le hw hz
  simp only [hzero, norm_zero, zero_pow (by omega : 3 ≠ 0), mul_zero, zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

example (n : ℕ) (a b : E) :
    max ‖a‖ ‖b‖ ^ n * ‖a - b‖ ≤ 2 * ‖radialPower n a - radialPower n b‖ :=
  max_norm_pow_mul_norm_sub_le n a b

example (a b : E) :
    ‖radialPower 6 a - radialPower 6 b‖ ≤
      2 * max ‖a‖ ‖b‖ ^ 3 * ‖radialPower 3 a - radialPower 3 b‖ :=
  norm_radialPower_double_sub_le 3 a b

example (a : E) : ‖a - (0 : E)‖ ≤ 2 * ‖a - (0 : E)‖ := by
  simpa [radialPower] using max_norm_pow_mul_norm_sub_le 0 a (0 : E)

#print axioms Mettapedia.Analysis.RadialPower.norm_radialPower
#print axioms Mettapedia.Analysis.RadialPower.radial_gap_mul_norm_le
#print axioms Mettapedia.Analysis.RadialPower.max_norm_pow_mul_norm_sub_le
#print axioms Mettapedia.Analysis.RadialPower.norm_radialPower_double_sub_le
