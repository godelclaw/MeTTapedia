import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smooth symmetric amplitude retention with a bounded complement

The rational weight is smooth at zero and at equal endpoint amplitudes.
Its complement times the smaller endpoint norm is at most the threshold.
It is not a sharp high-amplitude indicator: small nonzero inputs retain
a nonzero weight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudeCutoff

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E]

def retainedWeight (L : ℝ) (a : E) : ℝ := ‖a‖ ^ 2 / (L ^ 2 + ‖a‖ ^ 2)

def pairWeight (L : ℝ) (a b : E) : ℝ := retainedWeight L a * retainedWeight L b

def complementWeight (L : ℝ) (a b : E) : ℝ := 1 - pairWeight L a b

theorem denominator_pos (L : ℝ) (hL : 0 < L) (a : E) : 0 < L ^ 2 + ‖a‖ ^ 2 := by positivity

theorem retainedWeight_nonneg (L : ℝ) (a : E) : 0 ≤ retainedWeight L a := by
  unfold retainedWeight
  positivity

theorem retainedWeight_le_one (L : ℝ) (hL : 0 < L) (a : E) : retainedWeight L a ≤ 1 := by
  apply (div_le_one (denominator_pos L hL a)).mpr
  nlinarith [sq_nonneg L]

theorem pairWeight_nonneg (L : ℝ) (a b : E) : 0 ≤ pairWeight L a b :=
  mul_nonneg (retainedWeight_nonneg L a) (retainedWeight_nonneg L b)

theorem pairWeight_le_one (L : ℝ) (hL : 0 < L) (a b : E) : pairWeight L a b ≤ 1 := by
  exact (mul_le_mul (retainedWeight_le_one L hL a) (retainedWeight_le_one L hL b)
    (retainedWeight_nonneg L b) zero_le_one).trans_eq (one_mul 1)

theorem complementWeight_nonneg (L : ℝ) (hL : 0 < L) (a b : E) :
    0 ≤ complementWeight L a b := sub_nonneg.mpr (pairWeight_le_one L hL a b)

theorem complementWeight_le_one (L : ℝ) (a b : E) : complementWeight L a b ≤ 1 :=
  sub_le_self _ (pairWeight_nonneg L a b)

theorem pairWeight_swap (L : ℝ) (a b : E) : pairWeight L b a = pairWeight L a b := mul_comm _ _

theorem one_sub_retainedWeight (L : ℝ) (hL : 0 < L) (a : E) :
    1 - retainedWeight L a = L ^ 2 / (L ^ 2 + ‖a‖ ^ 2) := by
  unfold retainedWeight
  field_simp [(denominator_pos L hL a).ne']
  ring

theorem norm_mul_one_sub_retainedWeight_le (L : ℝ) (hL : 0 < L) (a : E) :
    ‖a‖ * (1 - retainedWeight L a) ≤ L / 2 := by
  rw [one_sub_retainedWeight L hL a, ← mul_div_assoc]
  apply (div_le_iff₀ (denominator_pos L hL a)).mpr
  nlinarith [sq_nonneg (‖a‖ - L)]

theorem complementWeight_le_sum (L : ℝ) (hL : 0 < L) (a b : E) :
    complementWeight L a b ≤ (1 - retainedWeight L a) + (1 - retainedWeight L b) := by
  have h := mul_nonneg (sub_nonneg.mpr (retainedWeight_le_one L hL a))
    (sub_nonneg.mpr (retainedWeight_le_one L hL b))
  unfold complementWeight pairWeight
  nlinarith only [h]

theorem complementWeight_mul_min_le (L : ℝ) (hL : 0 < L) (a b : E) :
    complementWeight L a b * min ‖a‖ ‖b‖ ≤ L := by
  calc
    _ ≤ ((1 - retainedWeight L a) + (1 - retainedWeight L b)) * min ‖a‖ ‖b‖ :=
      mul_le_mul_of_nonneg_right (complementWeight_le_sum L hL a b)
        (le_min (norm_nonneg a) (norm_nonneg b))
    _ = (1 - retainedWeight L a) * min ‖a‖ ‖b‖ +
        (1 - retainedWeight L b) * min ‖a‖ ‖b‖ := add_mul _ _ _
    _ ≤ (1 - retainedWeight L a) * ‖a‖ + (1 - retainedWeight L b) * ‖b‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _)
        (sub_nonneg.mpr (retainedWeight_le_one L hL a)))
        (mul_le_mul_of_nonneg_left (min_le_right _ _)
          (sub_nonneg.mpr (retainedWeight_le_one L hL b)))
    _ ≤ L / 2 + L / 2 := add_le_add
      (by simpa only [mul_comm] using norm_mul_one_sub_retainedWeight_le L hL a)
      (by simpa only [mul_comm] using norm_mul_one_sub_retainedWeight_le L hL b)
    _ = L := by ring

variable [InnerProductSpace ℝ E]

theorem contDiff_retainedWeight (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (retainedWeight L : E → ℝ) :=
  (contDiff_norm_sq ℝ).div (contDiff_const.add (contDiff_norm_sq ℝ))
    (fun a ↦ (denominator_pos L hL a).ne')

theorem contDiff_pairWeight (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (fun p : E × E ↦ pairWeight L p.1 p.2) :=
  ((contDiff_retainedWeight L hL).comp contDiff_fst).mul
    ((contDiff_retainedWeight L hL).comp contDiff_snd)

theorem contDiff_complementWeight (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (fun p : E × E ↦ complementWeight L p.1 p.2) :=
  contDiff_const.sub (contDiff_pairWeight L hL)

end Mettapedia.Analysis.SmoothAmplitudeCutoff
