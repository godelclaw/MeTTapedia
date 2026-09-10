import Mettapedia.Analysis.FiniteCoefficientEnergy
import Mathlib.Analysis.Complex.Basic

/-!
# Finite spectral resolvent energies

The multiplier `1 / (1 + epsilon * w)` contracts energy and gains one
weighted derivative at the sharp cost `1 / (4 * epsilon)`. Its squared
approximation error costs at most `epsilon / 4` times the first weighted
energy. The estimates do not count modes or assume a bound on their weights.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteResolventEnergy

open scoped BigOperators

variable {G : Type*}

def multiplier (epsilon w : ℝ) : ℝ := (1 + epsilon * w)⁻¹

def smooth (epsilon : ℝ) (w : G → ℝ) (c : G → ℂ) (q : G) : ℂ :=
  (multiplier epsilon (w q) : ℂ) * c q

theorem multiplier_pos {epsilon w : ℝ} (he : 0 ≤ epsilon) (hw : 0 ≤ w) :
    0 < multiplier epsilon w := inv_pos.mpr (by positivity)

theorem multiplier_le_one {epsilon w : ℝ} (he : 0 ≤ epsilon) (hw : 0 ≤ w) :
    multiplier epsilon w ≤ 1 := by
  unfold multiplier
  exact inv_le_one_of_one_le₀ (by nlinarith only [mul_nonneg he hw])

theorem four_mul_smoothing_le {epsilon w : ℝ} (he : 0 ≤ epsilon) (hw : 0 ≤ w) :
    4 * epsilon * w * multiplier epsilon w ^ 2 ≤ 1 := by
  have hd : 0 < 1 + epsilon * w := by positivity
  unfold multiplier
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hd)]
  nlinarith only [sq_nonneg (1 - epsilon * w)]

theorem sub_multiplier_eq {epsilon w : ℝ} (he : 0 ≤ epsilon) (hw : 0 ≤ w) :
    1 - multiplier epsilon w = epsilon * w * multiplier epsilon w := by
  have hd : 1 + epsilon * w ≠ 0 := ne_of_gt (by positivity)
  unfold multiplier
  field_simp
  ring

theorem squared_error_le {epsilon w : ℝ} (he : 0 ≤ epsilon) (hw : 0 ≤ w) :
    (1 - multiplier epsilon w) ^ 2 ≤ epsilon / 4 * w := by
  rw [sub_multiplier_eq he hw]
  have h := mul_le_mul_of_nonneg_left (four_mul_smoothing_le he hw) (mul_nonneg he hw)
  nlinarith only [h]

theorem weighted_smoothing_le {epsilon w : ℝ} (he : 0 < epsilon) (hw : 0 ≤ w) :
    w ^ 2 * multiplier epsilon w ^ 2 ≤ 1 / (4 * epsilon) * w := by
  have h := mul_le_mul_of_nonneg_left (four_mul_smoothing_le he.le hw) hw
  calc
    w ^ 2 * multiplier epsilon w ^ 2 ≤ w / (4 * epsilon) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [h])
    _ = 1 / (4 * epsilon) * w := by ring

theorem norm_smooth_sq (epsilon : ℝ) (w : G → ℝ) (c : G → ℂ) (q : G) :
    ‖smooth epsilon w c q‖ ^ 2 = multiplier epsilon (w q) ^ 2 * ‖c q‖ ^ 2 := by
  simp only [smooth, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem norm_sub_smooth_sq (epsilon : ℝ) (w : G → ℝ) (c : G → ℂ) (q : G) :
    ‖c q - smooth epsilon w c q‖ ^ 2 = (1 - multiplier epsilon (w q)) ^ 2 * ‖c q‖ ^ 2 := by
  have hid : c q - smooth epsilon w c q = ((1 - multiplier epsilon (w q) : ℝ) : ℂ) * c q := by
    simp only [smooth, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem energy_smooth_le (P : Finset G) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (w : G → ℝ) (hw : ∀ q ∈ P, 0 ≤ w q) (c : G → ℂ) :
    FiniteMultiplierLocalization.scalarEnergy P (smooth epsilon w c) ≤
      FiniteMultiplierLocalization.scalarEnergy P c := by
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_smooth_sq]
  have h := pow_le_pow_left₀ (multiplier_pos he (hw q hq)).le (multiplier_le_one he (hw q hq)) 2
  nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg ‖c q‖)]

theorem first_energy_smooth_le (P : Finset G) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (w : G → ℝ) (hw : ∀ q ∈ P, 0 ≤ w q) (c : G → ℂ) :
    (∑ q ∈ P, w q * ‖smooth epsilon w c q‖ ^ 2) ≤ ∑ q ∈ P, w q * ‖c q‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_smooth_sq]
  have h := pow_le_pow_left₀ (multiplier_pos he (hw q hq)).le (multiplier_le_one he (hw q hq)) 2
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg (hw q hq) (sq_nonneg ‖c q‖))
  nlinarith only [h']

theorem second_energy_smooth_le (P : Finset G) (epsilon : ℝ) (he : 0 < epsilon)
    (w : G → ℝ) (hw : ∀ q ∈ P, 0 ≤ w q) (c : G → ℂ) :
    (∑ q ∈ P, w q ^ 2 * ‖smooth epsilon w c q‖ ^ 2) ≤
      1 / (4 * epsilon) * ∑ q ∈ P, w q * ‖c q‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_smooth_sq]
  have h := mul_le_mul_of_nonneg_right (weighted_smoothing_le he (hw q hq)) (sq_nonneg ‖c q‖)
  nlinarith only [h]

theorem error_energy_le (P : Finset G) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (w : G → ℝ) (hw : ∀ q ∈ P, 0 ≤ w q) (c : G → ℂ) :
    FiniteMultiplierLocalization.scalarEnergy P (fun q ↦ c q - smooth epsilon w c q) ≤
      epsilon / 4 * ∑ q ∈ P, w q * ‖c q‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_sub_smooth_sq]
  have h := mul_le_mul_of_nonneg_right (squared_error_le he (hw q hq)) (sq_nonneg ‖c q‖)
  nlinarith only [h]

end Mettapedia.Analysis.FiniteResolventEnergy
