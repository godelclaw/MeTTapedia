import Mettapedia.Analysis.SmoothAmplitudePairing

/-!
# Bounded-kernel estimates for the retained signed source

This estimate is linear in the vorticity moment of order `n + 2` and in
the first vorticity moment. It is useful only for kernel pieces with a
genuine uniform bound; it does not bound the singular near interaction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudePairing

open MeasureTheory SignedCrossKernel SmoothAmplitudeCutoff RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem abs_retainedStretch_le_amplitudes (n : ℕ) (L : ℝ) (hL : 0 < L)
    (H : Op) (a b : R3) :
    |retainedStretch n L H a b| ≤
      ‖H‖ * (‖a‖ ^ (n + 2) * ‖b‖ + ‖b‖ ^ (n + 2) * ‖a‖) := by
  have hw : |retainedStretch n L H a b| ≤ |pairedStretch n H a b| := by
    rw [retainedStretch, abs_mul, abs_of_nonneg (pairWeight_nonneg L a b)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pairWeight_le_one L hL a b)
  calc
    _ ≤ _ := hw.trans (abs_pairedStretch_le n H a b)
    _ ≤ (‖a‖ * ‖b‖) * ‖H‖ * (‖radialPower n a‖ + ‖radialPower n b‖) := by
      gcongr
      · exact norm_cross_le a b
      · exact norm_sub_le _ _
    _ = _ := by simp only [norm_radialPower, pow_succ]; ring

theorem abs_half_integral_retained_le_of_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (H : X → X → Op) (w : X → R3)
    (n : ℕ) (L : ℝ) (hL : 0 < L) (C : ℝ)
    (hw : Integrable (fun x ↦ ‖w x‖) μ)
    (hp : Integrable (fun x ↦ ‖w x‖ ^ (n + 2)) μ)
    (hi : Integrable (fun p : X × X ↦ retainedStretch n L (H p.1 p.2)
      (w p.1) (w p.2)) (μ.prod μ))
    (hb : ∀ x y, ‖H x y‖ ≤ C) :
    |(1 / 2 : ℝ) * ∫ x, ∫ y, retainedStretch n L (H x y) (w x) (w y) ∂μ ∂μ| ≤
      C * (∫ x, ‖w x‖ ^ (n + 2) ∂μ) * ∫ x, ‖w x‖ ∂μ := by
  have hm := ((hp.mul_prod hw).add (hw.mul_prod hp)).const_mul C
  have hmajor (p : X × X) : |retainedStretch n L (H p.1 p.2) (w p.1) (w p.2)| ≤
      C * (‖w p.1‖ ^ (n + 2) * ‖w p.2‖ + ‖w p.1‖ * ‖w p.2‖ ^ (n + 2)) := by
    calc
      _ ≤ ‖H p.1 p.2‖ * (‖w p.1‖ ^ (n + 2) * ‖w p.2‖ + ‖w p.2‖ ^ (n + 2) * ‖w p.1‖) :=
        abs_retainedStretch_le_amplitudes n L hL (H p.1 p.2) (w p.1) (w p.2)
      _ ≤ C * (‖w p.1‖ ^ (n + 2) * ‖w p.2‖ + ‖w p.2‖ ^ (n + 2) * ‖w p.1‖) :=
        mul_le_mul_of_nonneg_right (hb p.1 p.2) (by positivity)
      _ = _ := by ring
  have he := integral_mono hi.abs hm hmajor
  simp only [Pi.add_apply] at he
  rw [integral_const_mul, integral_add (hp.mul_prod hw) (hw.mul_prod hp)] at he
  rw [integral_prod_mul (fun x ↦ ‖w x‖ ^ (n + 2)) (fun x ↦ ‖w x‖),
    integral_prod_mul (fun x ↦ ‖w x‖) (fun x ↦ ‖w x‖ ^ (n + 2))] at he
  rw [← integral_prod _ hi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ha := abs_integral_le_integral_abs (μ := μ.prod μ)
    (f := fun p : X × X ↦ retainedStretch n L (H p.1 p.2) (w p.1) (w p.2))
  nlinarith only [he, ha]

end Mettapedia.Analysis.SmoothAmplitudePairing
