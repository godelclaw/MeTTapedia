import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionSecant
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalKernel
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Direction differences of the actual pressure kernels

An exact secant identity, not pointwise multiplier comparison, transfers
the direction gap to inverse Fourier kernel moments. The physical changes
retain the quadratic mass gain and inverse input-scale first moment.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel

open MeasureTheory PressureDyadicKernel PressureDyadicPhysicalKernel
open PressureLowOutputCutoff (ratio)
open PressureLowOutputChange PressureLowOutputCoordinates
open Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SchwartzDilation
open scoped SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

theorem kernel_sub_eq_smul (t : ℝ) (e f w v : R3) (i : Fin 3) :
    kernel (t, e) w v i - kernel (t, f) w v i =
      ‖e - f‖ • 𝓕⁻ (PressureDirectionSecant.symbol
        (t, e, f, NormedSpace.normalize (e - f)) w v i) := by
  have h := congrArg (fun s : 𝓢(E6, ℂ) ↦ 𝓕⁻ s)
    (PressureDirectionSecant.symbol_sub_eq_smul t e f (NormedSpace.normalize (e - f)) w v i
      ‖e - f‖ (NormedSpace.norm_smul_normalize (e - f)).symm)
  simpa only [kernel, sub_eq_add_neg, FourierTransform.fourierInv_add,
    FourierTransform.fourierInv_neg, FourierTransform.fourierInv_smul] using h

theorem exists_uniform_moment (w v : R3) (i : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3,
      ‖e‖ ≤ 1 → ‖f‖ ≤ 1 →
      (∫ x : E6, ‖x‖ ^ m * ‖kernel (t, e) w v i x - kernel (t, f) w v i x‖) ≤
        ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := PressureDirectionSecant.exists_uniform_moment w v i m
  refine ⟨C, hC, ?_⟩
  intro t ht e f he hf
  have hh : ‖NormedSpace.normalize (e - f)‖ ≤ 1 := by
    by_cases h : e - f = 0
    · simp [h]
    · exact (NormedSpace.norm_normalize h).le
  have hid (x : E6) : kernel (t, e) w v i x - kernel (t, f) w v i x =
      ‖e - f‖ • (𝓕⁻ (PressureDirectionSecant.symbol
        (t, e, f, NormedSpace.normalize (e - f)) w v i)) x :=
    congrArg (fun s : 𝓢(E6, ℂ) ↦ s x) (kernel_sub_eq_smul t e f w v i)
  simp_rw [hid, norm_smul, Real.norm_of_nonneg (norm_nonneg (e - f)), mul_left_comm (‖_‖ ^ m)]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hb t ht e f _ he hf hh) (norm_nonneg _)

theorem exists_uniform_basis_moment (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3,
      ‖e‖ ≤ 1 → ‖f‖ ≤ 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ ^ m * ‖kernel (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x -
        kernel (t, f) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤
          ‖e - f‖ * C := by
  classical
  choose C hC hb using fun a : Fin 3 × Fin 3 × Fin 3 ↦
    exists_uniform_moment (EuclideanSpace.single a.2.1 1)
      (EuclideanSpace.single a.2.2 1) a.1 m
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), ?_⟩
  intro t ht e f he hf i j l
  exact (hb (i, j, l) t ht e f he hf).trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun a _ ↦ hC a) (Finset.mem_univ (i, j, l))) (norm_nonneg _))

theorem retainedKernel_sub (t : ℝ) (e f w v : R3) (i : Fin 3) :
    retainedKernel (t, e) w v i - retainedKernel (t, f) w v i =
      (ratio t) ^ 2 • (kernel (t, e) w v i - kernel (t, f) w v i) := by
  rw [retainedKernel, retainedKernel, smul_sub]

theorem physicalKernel_sub (t : ℝ) (e f w v : R3) (i : Fin 3) (ht : ratio t ≠ 0) :
    physicalKernel (t, e) w v i - physicalKernel (t, f) w v i =
      pullback (spatialChange (ratio t) ht)
        (retainedKernel (t, e) w v i - retainedKernel (t, f) w v i) := by
  ext x
  simp [physicalKernel, ht, pullback_apply, smul_sub]

theorem scaledKernel_sub (N : ℝ) (hN : 0 < N) (t : ℝ) (e f w v : R3) (i : Fin 3) :
    scaledKernel N hN (t, e) w v i - scaledKernel N hN (t, f) w v i =
      dilate N hN.ne' (physicalKernel (t, e) w v i - physicalKernel (t, f) w v i) := by
  ext x
  simp [scaledKernel, dilate, pullback_apply, smul_sub]

theorem moment_retainedKernel_sub (t : ℝ) (e f w v : R3) (i : Fin 3) (m : ℕ) :
    (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel (t, e) w v i x - retainedKernel (t, f) w v i x‖) =
      (ratio t) ^ 2 * ∫ x : E6, ‖x‖ ^ m * ‖kernel (t, e) w v i x - kernel (t, f) w v i x‖ := by
  simp only [retainedKernel, smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (ratio t))]
  simp_rw [mul_left_comm (‖_‖ ^ m) ((ratio t) ^ 2)]
  exact integral_const_mul _ _

theorem exists_uniform_scaled_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖scaledKernel N hN (t, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x -
        scaledKernel N hN (t, f) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤
          (ratio t) ^ 2 * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_moment 0
  refine ⟨C, hC, ?_⟩
  intro N hN t ht e f he hf i j l
  change (∫ x : E6, ‖(scaledKernel N hN (t, e) _ _ i - scaledKernel N hN (t, f) _ _ i) x‖) ≤ _
  rw [scaledKernel_sub, mass_dilate]
  by_cases hr : ratio t = 0
  · simp [physicalKernel, hr]
  · rw [physicalKernel_sub t e f _ _ i hr, mass_pullback]
    have hm := moment_retainedKernel_sub t e f (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i 0
    simp only [pow_zero, one_mul] at hm
    change (∫ x : E6, ‖retainedKernel (t, e) _ _ i x - retainedKernel (t, f) _ _ i x‖) ≤ _
    rw [hm]
    have h := mul_le_mul_of_nonneg_left (hb t ht e f he hf i j l) (sq_nonneg (ratio t))
    simpa only [pow_zero, one_mul, mul_assoc] using h

theorem exists_uniform_scaled_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ * ‖scaledKernel N hN (t, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x -
        scaledKernel N hN (t, f) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤
          (ratio t / N) * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_moment 1
  refine ⟨3 * C, by positivity, ?_⟩
  intro N hN t ht e f he hf i j l
  let w : R3 := EuclideanSpace.single j 1
  let v : R3 := EuclideanSpace.single l 1
  change (∫ x : E6, ‖x‖ * ‖(scaledKernel N hN (t, e) w v i - scaledKernel N hN (t, f) w v i) x‖) ≤ _
  rw [scaledKernel_sub]
  have hd := moment_dilate N hN.ne'
    (physicalKernel (t, e) w v i - physicalKernel (t, f) w v i) 1
  simp only [pow_one, abs_of_pos hN] at hd
  rw [hd]
  by_cases hr : ratio t = 0
  · simp [physicalKernel, hr]
  have hrp : 0 < ratio t := lt_of_le_of_ne (div_nonneg ht.1 (by norm_num)) (Ne.symm hr)
  have hru : ratio t ≤ 1 := by unfold ratio; linarith [ht.2]
  rw [physicalKernel_sub t e f w v i hr]
  have hp := moment_pullback_le (spatialChange (ratio t) hr)
    (retainedKernel (t, e) w v i - retainedKernel (t, f) w v i) 1
  simp only [pow_one] at hp
  have hm : (∫ x : E6, ‖x‖ * ‖(retainedKernel (t, e) w v i - retainedKernel (t, f) w v i) x‖) ≤
      (ratio t) ^ 2 * (‖e - f‖ * C) := by
    have heq := moment_retainedKernel_sub t e f w v i 1
    simp only [pow_one] at heq
    rw [show (fun x : E6 ↦ ‖x‖ * ‖(retainedKernel (t, e) w v i - retainedKernel (t, f) w v i) x‖) =
      (fun x : E6 ↦ ‖x‖ * ‖retainedKernel (t, e) w v i x - retainedKernel (t, f) w v i x‖) from rfl, heq]
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hb t ht e f he hf i j l)
      (sq_nonneg _)
  calc
    _ ≤ N⁻¹ * ((3 / ratio t) * ((ratio t) ^ 2 * (‖e - f‖ * C))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
      exact hp.trans (mul_le_mul (opNorm_spatialChange_symm_le _ hrp hru) hm
        (integral_nonneg (fun _ ↦ by positivity)) (by positivity))
    _ = _ := by field_simp

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel
