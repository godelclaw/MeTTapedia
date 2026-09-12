import Mettapedia.Analysis.RadialRieszHessian

/-!
# Uniform spatial moments of the radial Riesz family

The compact radial regularizer is an exact finite sum of dilates of its
lowest annulus. Positive spatial moments therefore have geometric bounds
independent of the highest frequency cutoff. Periodization and nonlinear
time estimates are separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open MeasureTheory SchwartzDilation
open scoped SchwartzMap FourierTransform

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem weight_succ (N : ℕ) (x : Rd) :
    weight (N + 1) x = weight N x + weight 0 (((1 / 2 : ℝ) ^ (N + 1)) • x) := by
  simp only [weight_eq_lowPass_sub, pow_zero, smul_smul, one_mul]
  have he : (2 : ℝ) * (1 / 2) ^ (N + 1) = (1 / 2) ^ N := by rw [pow_succ]; ring
  rw [he]
  ring

theorem weight_eq_sum (N : ℕ) (x : Rd) :
    weight N x = ∑ n ∈ Finset.range (N + 1), weight 0 (((1 / 2 : ℝ) ^ n) • x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← ih, weight_succ]

def dyadicKernel (i j : Fin d) (n : ℕ) : 𝓢(Rd, ℂ) :=
  dilate ((2 : ℝ) ^ n) (by positivity) (kernel 0 i j)

theorem fourier_dyadicKernel (i j : Fin d) (n : ℕ) (x : Rd) :
    (𝓕 (dyadicKernel i j n)) x =
      ((weight 0 (((1 / 2 : ℝ) ^ n) • x) * AnnularRieszKernel.rieszEntry i j x : ℝ) : ℂ) := by
  rw [dyadicKernel, fourier_dilate, fourier_kernel_apply,
    AnnularRieszKernel.rieszEntry_smul i j _ (by positivity)]
  simp only [inv_pow, one_div]

theorem kernel_eq_sum (N : ℕ) (i j : Fin d) :
    kernel N i j = ∑ n ∈ Finset.range (N + 1), dyadicKernel i j n := by
  have he : 𝓕 (kernel N i j) = 𝓕 (∑ n ∈ Finset.range (N + 1), dyadicKernel i j n) := by
    ext x
    simp only [FourierTransform.fourier_sum, sum_apply, fourier_dyadicKernel,
      fourier_kernel_apply, weight_eq_sum N x, Finset.sum_mul, Complex.ofReal_sum]
  calc
    _ = 𝓕⁻ (𝓕 (kernel N i j)) := (FourierTransform.fourierInv_fourier_eq _).symm
    _ = _ := congrArg (fun f : 𝓢(Rd, ℂ) ↦ 𝓕⁻ f) he
    _ = _ := FourierTransform.fourierInv_fourier_eq _

def baseMoment (m : ℕ) (i j : Fin d) : ℝ := ∫ x : Rd, ‖x‖ ^ m * ‖kernel 0 i j x‖

theorem baseMoment_nonneg (m : ℕ) (i j : Fin d) : 0 ≤ baseMoment m i j :=
  integral_nonneg (fun _ ↦ by positivity)

theorem moment_dyadicKernel (m : ℕ) (i j : Fin d) (n : ℕ) :
    (∫ x : Rd, ‖x‖ ^ m * ‖dyadicKernel i j n x‖) =
      ((1 / 2 : ℝ) ^ m) ^ n * baseMoment m i j := by
  rw [dyadicKernel, moment_dilate, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ n), inv_pow]
  simp only [one_div, ← pow_mul, mul_comm n m, baseMoment]
  rw [inv_pow]

theorem moment_kernel_le (N m : ℕ) (hm : 0 < m) (i j : Fin d) :
    (∫ x : Rd, ‖x‖ ^ m * ‖kernel N i j x‖) ≤
      (1 - (1 / 2 : ℝ) ^ m)⁻¹ * baseMoment m i j := by
  have hi (n : ℕ) : Integrable (fun x : Rd ↦ ‖x‖ ^ m * ‖dyadicKernel i j n x‖) :=
    (dyadicKernel i j n).integrable_pow_mul volume m
  have hr : ‖(1 / 2 : ℝ) ^ m‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hs := hasSum_geometric_of_norm_lt_one hr
  have hsum := hs.summable.sum_le_tsum (Finset.range (N + 1)) (fun _ _ ↦ by positivity)
  rw [hs.tsum_eq] at hsum
  calc
    _ ≤ ∫ x : Rd, ∑ n ∈ Finset.range (N + 1), ‖x‖ ^ m * ‖dyadicKernel i j n x‖ := by
      apply integral_mono ((kernel N i j).integrable_pow_mul volume m)
        (integrable_finsetSum _ (fun n _ ↦ hi n))
      intro x
      change ‖x‖ ^ m * ‖kernel N i j x‖ ≤ ∑ n ∈ Finset.range (N + 1), ‖x‖ ^ m * ‖dyadicKernel i j n x‖
      rw [kernel_eq_sum]
      simp only [sum_apply, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ n ∈ Finset.range (N + 1), ((1 / 2 : ℝ) ^ m) ^ n * baseMoment m i j := by
      rw [integral_finsetSum _ (fun n _ ↦ hi n)]
      simp only [moment_dyadicKernel]
    _ = (∑ n ∈ Finset.range (N + 1), ((1 / 2 : ℝ) ^ m) ^ n) * baseMoment m i j :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (baseMoment_nonneg m i j)

theorem firstMoment_kernel_le (N : ℕ) (i j : Fin d) :
    (∫ x : Rd, ‖x‖ * ‖kernel N i j x‖) ≤ 2 * baseMoment 1 i j := by
  convert moment_kernel_le N 1 (by decide) i j using 1 <;> norm_num

theorem secondMoment_kernel_le (N : ℕ) (i j : Fin d) :
    (∫ x : Rd, ‖x‖ ^ 2 * ‖kernel N i j x‖) ≤ (4 / 3 : ℝ) * baseMoment 2 i j := by
  convert moment_kernel_le N 2 (by decide) i j using 1
  norm_num

end Mettapedia.Analysis.RadialRieszRegularization
