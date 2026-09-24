import Mettapedia.Analysis.DyadicHighPass
import Mettapedia.Analysis.SchwartzDilation
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Smooth annular kernels for the second-order Riesz symbol

The buffered denominator makes the compact annular symbol globally smooth,
while retaining exactly `xi_i xi_j / |xi|^2` on its support. Its inverse
Fourier transform is a Schwartz kernel. Dyadic dilation gives a summable
second-moment bound for finite sums, uniformly in the highest scale.
The lowest scale is one half, so the resulting annuli cover every nonzero
integer frequency, including frequencies of norm one.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AnnularRieszKernel

open MeasureTheory DyadicAnnulus SchwartzDilation
open scoped SchwartzMap FourierTransform ContDiff Topology

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

def rieszEntry (i j : Fin d) (x : Rd) : ℝ := x i * x j / ‖x‖ ^ 2

@[simp] theorem rieszEntry_neg (i j : Fin d) (x : Rd) : rieszEntry i j (-x) = rieszEntry i j x := by
  simp [rieszEntry]

theorem normalizedCutoff_neg (x : Rd) : normalizedCutoff (-x) = normalizedCutoff x := by
  simp only [normalizedCutoff, normalizer, band, SmoothAnnulus.cutoff, smul_neg, ContDiffBump.neg]

def weight (N : ℕ) (x : Rd) : ℝ :=
  ∑ n ∈ Finset.range N, normalizedCutoff ((1 / 2 : ℝ) ^ n • ((2 : ℝ) • x))

theorem weight_nonneg (N : ℕ) (x : Rd) : 0 ≤ weight N x :=
  Finset.sum_nonneg (fun _ _ ↦ normalizedCutoff_nonneg _)

theorem weight_le_one (N : ℕ) (x : Rd) : weight N x ≤ 1 := by
  have h := DyadicHighPass.hasSum_annuli ((2 : ℝ) • x)
  have hb := h.summable.sum_le_tsum (Finset.range N) (fun _ _ ↦ normalizedCutoff_nonneg _)
  rw [h.tsum_eq] at hb
  exact hb.trans (DyadicHighPass.multiplier_le_one _)

@[simp] theorem weight_neg (N : ℕ) (x : Rd) : weight N (-x) = weight N x := by
  simp only [weight, smul_neg, normalizedCutoff_neg]

theorem tendsto_weight (x : Rd) (hx : 1 ≤ ‖x‖) :
    Filter.Tendsto (fun N : ℕ ↦ weight N x) Filter.atTop (𝓝 1) := by
  have h := (DyadicHighPass.hasSum_annuli ((2 : ℝ) • x)).tendsto_sum_nat
  rw [DyadicHighPass.multiplier_eq_one_of_le_norm _ (by
    rw [norm_smul]; norm_num only [Real.norm_ofNat]; linarith)] at h
  exact h

def entry (i j : Fin d) (x : Rd) : ℝ :=
  normalizedCutoff x * (x i * x j / SmoothAnnulus.denominator x)

theorem entry_eq_cutoff_mul (i j : Fin d) (x : Rd) :
    entry i j x = normalizedCutoff x * rieszEntry i j x := by
  by_cases hx : normalizedCutoff x = 0
  · simp [entry, hx]
  · rw [entry, SmoothAnnulus.denominator_eq_norm_sq x
      (cutoff_ne_zero_of_normalizedCutoff_ne_zero x hx)]
    rfl

theorem contDiff_entry (i j : Fin d) : ContDiff ℝ ∞ (entry i j) := by
  have hi : ContDiff ℝ ∞ (fun x : Rd ↦ x i) := by fun_prop
  have hj : ContDiff ℝ ∞ (fun x : Rd ↦ x j) := by fun_prop
  have hd : ContDiff ℝ ∞ (SmoothAnnulus.denominator (E := Rd)) :=
    (contDiff_norm_sq ℝ).add (contDiff_const.sub SmoothAnnulus.contDiff_buffer)
  exact contDiff_normalizedCutoff.mul ((hi.mul hj).div hd
    (fun x ↦ (SmoothAnnulus.denominator_pos x).ne'))

theorem hasCompactSupport_entry (i j : Fin d) : HasCompactSupport (entry i j) :=
  hasCompactSupport_normalizedCutoff.mul_right

def symbol (i j : Fin d) : 𝓢(Rd, ℂ) :=
  ((hasCompactSupport_entry i j).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_entry i j))

@[simp] theorem symbol_apply (i j : Fin d) (x : Rd) : symbol i j x = (entry i j x : ℂ) := rfl

def kernel (i j : Fin d) : 𝓢(Rd, ℂ) := 𝓕⁻ (symbol i j)

@[simp] theorem fourier_kernel (i j : Fin d) : 𝓕 (kernel i j) = symbol i j :=
  FourierTransform.fourier_fourierInv_eq _

theorem rieszEntry_smul (i j : Fin d) (r : ℝ) (hr : r ≠ 0) (x : Rd) :
    rieszEntry i j (r • x) = rieszEntry i j x := by
  simp only [rieszEntry, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  · field_simp

def scale (n : ℕ) : ℝ := (2 : ℝ) ^ n / 2

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

theorem inv_scale (n : ℕ) : (scale n)⁻¹ = (1 / 2 : ℝ) ^ n * 2 := by
  simp [scale, div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm]

def dyadicKernel (i j : Fin d) (n : ℕ) : 𝓢(Rd, ℂ) :=
  dilate (scale n) (scale_pos n).ne' (kernel i j)

theorem fourier_dyadicKernel (i j : Fin d) (n : ℕ) (x : Rd) :
    (𝓕 (dyadicKernel i j n)) x =
      ((normalizedCutoff ((1 / 2 : ℝ) ^ n • ((2 : ℝ) • x)) * rieszEntry i j x : ℝ) : ℂ) := by
  rw [dyadicKernel, fourier_dilate, fourier_kernel, symbol_apply, entry_eq_cutoff_mul,
    rieszEntry_smul i j _ (inv_ne_zero (scale_pos n).ne'), inv_scale, mul_smul]

def secondMoment (i j : Fin d) : ℝ := ∫ x : Rd, ‖x‖ ^ 2 * ‖kernel i j x‖

theorem secondMoment_nonneg (i j : Fin d) : 0 ≤ secondMoment i j :=
  integral_nonneg (fun _ ↦ by positivity)

theorem secondMoment_dyadicKernel (i j : Fin d) (n : ℕ) :
    (∫ x : Rd, ‖x‖ ^ 2 * ‖dyadicKernel i j n x‖) =
      4 * (1 / 4 : ℝ) ^ n * secondMoment i j := by
  rw [dyadicKernel, moment_dilate, abs_of_pos (scale_pos n), inv_scale, mul_pow]
  rw [← pow_mul, mul_comm n 2, pow_mul]
  norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num, show (2 : ℝ) ^ 2 = 4 by norm_num]
  unfold secondMoment
  ring

/-- The Fourier symbols reconstruct the Riesz entry wherever `|x| >= 1`. -/
theorem hasSum_fourier_dyadicKernel (i j : Fin d) (x : Rd) (hx : 1 ≤ ‖x‖) :
    HasSum (fun n : ℕ ↦ (𝓕 (dyadicKernel i j n)) x) (rieszEntry i j x : ℂ) := by
  have h := (DyadicHighPass.hasSum_annuli ((2 : ℝ) • x)).mul_right (rieszEntry i j x)
  rw [DyadicHighPass.multiplier_eq_one_of_le_norm _ (by
    rw [norm_smul]; norm_num only [Real.norm_ofNat]; linarith), one_mul] at h
  have hc := Complex.ofRealCLM.hasSum h
  simpa only [fourier_dyadicKernel, Complex.ofRealCLM_apply] using hc

def partialKernel (i j : Fin d) (N : ℕ) : 𝓢(Rd, ℂ) :=
  ∑ n ∈ Finset.range N, dyadicKernel i j n

theorem fourier_partialKernel (i j : Fin d) (N : ℕ) (x : Rd) :
    (𝓕 (partialKernel i j N)) x = ((weight N x * rieszEntry i j x : ℝ) : ℂ) := by
  simp only [partialKernel, FourierTransform.fourier_sum, sum_apply, fourier_dyadicKernel,
    weight, Finset.sum_mul, Complex.ofReal_sum]

theorem secondMoment_partialKernel_le (i j : Fin d) (N : ℕ) :
    (∫ x : Rd, ‖x‖ ^ 2 * ‖partialKernel i j N x‖) ≤ (16 / 3) * secondMoment i j := by
  have hi (n : ℕ) : Integrable (fun x : Rd ↦ ‖x‖ ^ 2 * ‖dyadicKernel i j n x‖) :=
    (dyadicKernel i j n).integrable_pow_mul volume 2
  have hp : (∫ x : Rd, ‖x‖ ^ 2 * ‖partialKernel i j N x‖) ≤
      ∑ n ∈ Finset.range N, 4 * (1 / 4 : ℝ) ^ n * secondMoment i j := by
    simp_rw [← secondMoment_dyadicKernel]
    rw [← integral_finsetSum _ (fun n _ ↦ hi n)]
    apply integral_mono ((partialKernel i j N).integrable_pow_mul volume 2)
      (integrable_finsetSum _ (fun n _ ↦ hi n))
    intro x
    simp only [partialKernel, sum_apply, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
  have hs : (∑ n ∈ Finset.range N, (1 / 4 : ℝ) ^ n) ≤ 4 / 3 := by
    have h := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1))
    have hb := h.summable.sum_le_tsum (Finset.range N) (fun n _ ↦ by positivity)
    rw [h.tsum_eq] at hb
    norm_num at hb ⊢
    exact hb
  calc
    _ ≤ _ := hp
    _ = (4 * secondMoment i j) * ∑ n ∈ Finset.range N, (1 / 4 : ℝ) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (4 * secondMoment i j) * (4 / 3) :=
      mul_le_mul_of_nonneg_left hs (by positivity [secondMoment_nonneg i j])
    _ = _ := by ring

end Mettapedia.Analysis.AnnularRieszKernel
