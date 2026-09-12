import Mettapedia.Analysis.SignedCrossKernel
import Mettapedia.Analysis.AbsolutelyContinuousComposition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Interface-safe regularity of the high-amplitude weight

The cutoff is globally Lipschitz, including its threshold and equal-amplitude
interfaces. Its composition with absolutely continuous endpoint paths is
absolutely continuous, so its almost-everywhere derivative accounts for the
whole endpoint change. No assumption that the interfaces have measure zero
is made.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open MeasureTheory
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem lipschitzWith_one_sub_div_max (L : ℝ) (hL : 0 < L) :
    LipschitzWith (Real.toNNReal (1 / L)) (fun r : ℝ ↦ 1 - L / max L r) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have hr : 0 < max L r := hL.trans_le (le_max_left _ _)
  have hs : 0 < max L s := hL.trans_le (le_max_left _ _)
  have hden : L * L ≤ max L r * max L s :=
    mul_le_mul (le_max_left _ _) (le_max_left _ _) hL.le hr.le
  have hd : |max L r - max L s| ≤ |r - s| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using
      (LipschitzWith.id.const_max L).dist_le_mul r s
  have he : (1 - L / max L r) - (1 - L / max L s) =
      L * (max L r - max L s) / (max L r * max L s) := by
    field_simp [hr.ne', hs.ne']
    ring
  rw [Real.toNNReal_of_nonneg (by positivity), Real.dist_eq, Real.dist_eq, he,
    abs_div, abs_mul, abs_of_pos hL, abs_of_pos (mul_pos hr hs)]
  calc
    _ ≤ L * |max L r - max L s| / (L * L) :=
      div_le_div_of_nonneg_left (mul_nonneg hL.le (abs_nonneg _)) (mul_pos hL hL) hden
    _ = (1 / L) * |max L r - max L s| := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

theorem lipschitzWith_highAmplitudeWeight (L : ℝ) (hL : 0 < L) :
    LipschitzWith (Real.toNNReal (1 / L))
      (fun p : R3 × R3 ↦ 1 - lowAmplitudeWeight L p.1 p.2) := by
  have ha : LipschitzWith 1 (fun p : R3 × R3 ↦ ‖p.1‖) :=
    by simpa only [one_mul, Function.comp_def] using lipschitzWith_one_norm.comp LipschitzWith.prod_fst
  have hb : LipschitzWith 1 (fun p : R3 × R3 ↦ ‖p.2‖) :=
    by simpa only [one_mul, Function.comp_def] using lipschitzWith_one_norm.comp LipschitzWith.prod_snd
  simpa only [lowAmplitudeWeight, Function.comp_def, max_self, mul_one] using
    (lipschitzWith_one_sub_div_max L hL).comp (ha.min hb)

theorem absolutelyContinuousOnInterval_highAmplitudeWeight {u v : ℝ → R3} {a b L : ℝ}
    (hL : 0 < L) (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ 1 - lowAmplitudeWeight L (u t) (v t)) a b :=
  AbsolutelyContinuousComposition.comp_lipschitz (u := fun t ↦ (u t, v t))
    (lipschitzWith_highAmplitudeWeight L hL)
    (AbsolutelyContinuousComposition.prodMk hu hv)

theorem integral_deriv_highAmplitudeWeight_eq_sub {u v : ℝ → R3} {a b L : ℝ}
    (hL : 0 < L) (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b) :
    (∫ t in a..b, deriv (fun τ ↦ 1 - lowAmplitudeWeight L (u τ) (v τ)) t) =
      (1 - lowAmplitudeWeight L (u b) (v b)) - (1 - lowAmplitudeWeight L (u a) (v a)) :=
  (absolutelyContinuousOnInterval_highAmplitudeWeight hL hu hv).integral_deriv_eq_sub

theorem absolutelyContinuousOnInterval_highAmplitudeProduct {u v : ℝ → R3} {Q : ℝ → ℝ}
    {a b L : ℝ} (hL : 0 < L) (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b) (hQ : AbsolutelyContinuousOnInterval Q a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (1 - lowAmplitudeWeight L (u t) (v t)) * Q t) a b :=
  (absolutelyContinuousOnInterval_highAmplitudeWeight hL hu hv).mul hQ

end Mettapedia.Analysis.SignedCrossKernel
