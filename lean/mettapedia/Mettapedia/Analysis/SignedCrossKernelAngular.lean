import Mettapedia.Analysis.SignedCrossKernel

/-!
# A dissipation-compatible price for angular stretching

Young's inequality separates a cubic radial increment from a weighted
cross-product cost. A dimension-three kernel bound and a projective
Lipschitz direction bound then make the angular cost a product of the
eighth vorticity moment and enstrophy. No direction bound is inferred
from the algebra.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open RadialPower EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def angularCost (n : ℕ) (r : ℝ) (H : Op) (a b : R3) : ℝ :=
  r * ‖H‖ * max ‖a‖ ‖b‖ ^ (2 * n) * ‖cross a b‖ ^ 2

theorem angularCost_nonneg (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (H : Op) (a b : R3) :
    0 ≤ angularCost n r H a b := by unfold angularCost; positivity

/-- One spatial distance is allocated to each side of the Young pairing. -/
theorem abs_pairedStretch_le_increment_add_angular (n : ℕ)
    (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (H : Op) (a b : R3) :
    |pairedStretch (2 * n) H a b| ≤
      ε * (‖H‖ / r * ‖radialPower n a - radialPower n b‖ ^ 2) +
        ε⁻¹ * angularCost n r H a b := by
  have hy : 2 * (max ‖a‖ ‖b‖ ^ n * ‖cross a b‖) *
      ‖radialPower n a - radialPower n b‖ ≤
        ε / r * ‖radialPower n a - radialPower n b‖ ^ 2 +
          r / ε * (max ‖a‖ ‖b‖ ^ n * ‖cross a b‖) ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < ε * r by positivity)).mp
    field_simp
    nlinarith only [sq_nonneg (ε * ‖radialPower n a - radialPower n b‖ -
      r * (max ‖a‖ ‖b‖ ^ n * ‖cross a b‖))]
  calc
    _ ≤ ‖cross a b‖ * ‖H‖ *
        (2 * max ‖a‖ ‖b‖ ^ n * ‖radialPower n a - radialPower n b‖) := by
      apply (abs_pairedStretch_le (2 * n) H a b).trans
      exact mul_le_mul_of_nonneg_left (norm_radialPower_double_sub_le n a b) (by positivity)
    _ = ‖H‖ * (2 * (max ‖a‖ ‖b‖ ^ n * ‖cross a b‖) *
        ‖radialPower n a - radialPower n b‖) := by ring
    _ ≤ ‖H‖ * (ε / r * ‖radialPower n a - radialPower n b‖ ^ 2 +
        r / ε * (max ‖a‖ ‖b‖ ^ n * ‖cross a b‖) ^ 2) :=
      mul_le_mul_of_nonneg_left hy (norm_nonneg H)
    _ = _ := by
      simp only [angularCost, mul_pow, div_eq_mul_inv, pow_mul, mul_comm 2 n]
      ring

/-- Projective coherence is stated without normalizing or dividing by either
endpoint vorticity. Thus zeros and opposite orientations are included. -/
theorem angularCost_le_of_cross_bound (n : ℕ) (r K C : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (H : Op) (a b : R3)
    (hH : r ^ 3 * ‖H‖ ≤ C)
    (hc : ‖cross a b‖ ≤ K * r * ‖a‖ * ‖b‖) :
    angularCost n r H a b ≤ K ^ 2 * C *
      (‖a‖ ^ (2 * n + 2) * ‖b‖ ^ 2 + ‖a‖ ^ 2 * ‖b‖ ^ (2 * n + 2)) := by
  have hmax : max ‖a‖ ‖b‖ ^ (2 * n) ≤ ‖a‖ ^ (2 * n) + ‖b‖ ^ (2 * n) := by
    rcases le_total ‖b‖ ‖a‖ with h | h
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ r * ‖H‖ * max ‖a‖ ‖b‖ ^ (2 * n) * (K * r * ‖a‖ * ‖b‖) ^ 2 := by
      unfold angularCost
      gcongr
    _ = K ^ 2 * (r ^ 3 * ‖H‖) * max ‖a‖ ‖b‖ ^ (2 * n) * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring
    _ ≤ K ^ 2 * C * (‖a‖ ^ (2 * n) + ‖b‖ ^ (2 * n)) * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
      gcongr
    _ = _ := by simp only [pow_add]; ring

end Mettapedia.Analysis.SignedCrossKernel
