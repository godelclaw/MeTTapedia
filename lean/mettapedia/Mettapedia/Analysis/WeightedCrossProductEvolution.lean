import Mettapedia.Analysis.SymmetricCrossProductStrain
import Mettapedia.Analysis.EuclideanCrossProductCalculus

/-!
# Weighted angular energy and its signed evolution

The symmetric polynomial weight is comparable, within a factor of two,
to the maximum-amplitude weight. Its derivative retains amplitude growth
as well as cross-product rotation. Decrease of normalized angle alone is
not an estimate on this weighted quantity. All identities include zeros.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCrossProduct

open EuclideanCrossProduct
open scoped RealInnerProductSpace ContDiff
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def amplitudeWeight (n : ℕ) (a b : R3) : ℝ :=
  ‖a‖ ^ (2 * (n + 1)) + ‖b‖ ^ (2 * (n + 1))

def energy (n : ℕ) (a b : R3) : ℝ := amplitudeWeight n a b * ‖cross a b‖ ^ 2

def amplitudeRate (n : ℕ) (a b v w : R3) : ℝ :=
  (2 * (n + 1) : ℝ) * (‖a‖ ^ (2 * n) * ⟪a, v⟫ + ‖b‖ ^ (2 * n) * ⟪b, w⟫)

def rate (n : ℕ) (a b v w : R3) : ℝ :=
  amplitudeRate n a b v w * ‖cross a b‖ ^ 2 +
    2 * amplitudeWeight n a b * ⟪cross a b, cross v b + cross a w⟫

theorem amplitudeWeight_nonneg (n : ℕ) (a b : R3) : 0 ≤ amplitudeWeight n a b := by
  unfold amplitudeWeight
  positivity

theorem energy_nonneg (n : ℕ) (a b : R3) : 0 ≤ energy n a b :=
  mul_nonneg (amplitudeWeight_nonneg n a b) (sq_nonneg _)

theorem energy_swap (n : ℕ) (a b : R3) : energy n b a = energy n a b := by
  simp only [energy, amplitudeWeight, cross_swap b a, norm_neg, add_comm]

theorem max_weight_le_energy (n : ℕ) (a b : R3) :
    max ‖a‖ ‖b‖ ^ (2 * (n + 1)) * ‖cross a b‖ ^ 2 ≤ energy n a b := by
  unfold energy amplitudeWeight
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rcases le_total ‖b‖ ‖a‖ with h | h
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)

theorem energy_le_two_max_weight (n : ℕ) (a b : R3) :
    energy n a b ≤ 2 * (max ‖a‖ ‖b‖ ^ (2 * (n + 1)) * ‖cross a b‖ ^ 2) := by
  have ha := pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ ‖b‖) (2 * (n + 1))
  have hb := pow_le_pow_left₀ (norm_nonneg b) (le_max_right ‖a‖ ‖b‖) (2 * (n + 1))
  have h := mul_le_mul_of_nonneg_right (add_le_add ha hb) (sq_nonneg ‖cross a b‖)
  simpa only [energy, amplitudeWeight, ← two_mul, mul_assoc] using h

theorem contDiff_energy (n : ℕ) : ContDiff ℝ ∞ (fun p : R3 × R3 ↦ energy n p.1 p.2) := by
  simp only [energy, amplitudeWeight, pow_mul]
  exact (((contDiff_fst.norm_sq ℝ).pow (n + 1)).add
    ((contDiff_snd.norm_sq ℝ).pow (n + 1))).mul (contDiff_cross.norm_sq ℝ)

theorem hasDerivAt_amplitudeWeight (n : ℕ) {a b : ℝ → R3} {v w : R3} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) :
    HasDerivAt (fun τ ↦ amplitudeWeight n (a τ) (b τ)) (amplitudeRate n (a t) (b t) v w) t := by
  have h := ((ha.norm_sq).pow (n + 1)).add ((hb.norm_sq).pow (n + 1))
  simp only [amplitudeWeight, pow_mul]
  apply h.congr_deriv
  simp only [amplitudeRate, Nat.add_sub_cancel, pow_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem hasDerivAt_energy (n : ℕ) {a b : ℝ → R3} {v w : R3} {t : ℝ}
    (ha : HasDerivAt a v t) (hb : HasDerivAt b w t) :
    HasDerivAt (fun τ ↦ energy n (a τ) (b τ)) (rate n (a t) (b t) v w) t := by
  have h := (hasDerivAt_amplitudeWeight n ha hb).mul ((hasDerivAt_cross ha hb).norm_sq)
  apply h.congr_deriv
  simp only [rate]
  ring

def strainRate (n : ℕ) (S T : Op) (a b : R3) : ℝ :=
  amplitudeRate n a b (S a) (T b) * ‖cross a b‖ ^ 2 -
    amplitudeWeight n a b * (⟪cross a b, S (cross a b)⟫ + ⟪cross a b, T (cross a b)⟫)

def perturbationRate (n : ℕ) (S T : Op) (a b f g : R3) : ℝ :=
  amplitudeRate n a b f g * ‖cross a b‖ ^ 2 +
    2 * amplitudeWeight n a b * ⟪cross a b, symmetricPairForcing S T a b f g⟫

theorem rate_eq_strain_add_perturbation (n : ℕ) (S T : Op) (a b f g : R3)
    (hS : cross (S a) b + cross a (S b) = -S (cross a b))
    (hT : cross (T b) a + cross b (T a) = -T (cross b a)) :
    rate n a b (S a + f) (T b + g) = strainRate n S T a b + perturbationRate n S T a b f g := by
  unfold rate
  rw [cross_rate_eq_symmetric S T a b f g hS hT]
  simp only [strainRate, perturbationRate, amplitudeRate, inner_add_right, real_inner_smul_right]
  ring

theorem perturbationRate_common_zero (n : ℕ) (S : Op) (a b : R3) :
    perturbationRate n S S a b 0 0 = 0 := by
  simp [perturbationRate, amplitudeRate, symmetricPairForcing_eq]

theorem hasDerivAt_energy_strain (n : ℕ) {a b : ℝ → R3} {t : ℝ}
    (S T : Op) (f g : R3)
    (ha : HasDerivAt a (S (a t) + f) t) (hb : HasDerivAt b (T (b t) + g) t)
    (hS : cross (S (a t)) (b t) + cross (a t) (S (b t)) = -S (cross (a t) (b t)))
    (hT : cross (T (b t)) (a t) + cross (b t) (T (a t)) = -T (cross (b t) (a t))) :
    HasDerivAt (fun τ ↦ energy n (a τ) (b τ))
      (strainRate n S T (a t) (b t) + perturbationRate n S T (a t) (b t) f g) t := by
  simpa only [rate_eq_strain_add_perturbation n S T (a t) (b t) f g hS hT] using
    hasDerivAt_energy n ha hb

end Mettapedia.Analysis.WeightedCrossProduct
