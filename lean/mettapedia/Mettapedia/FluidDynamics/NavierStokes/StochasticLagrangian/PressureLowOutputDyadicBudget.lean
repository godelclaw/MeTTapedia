import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputScaledKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summable physical low-output band costs

The actual band-kernel masses and first moments are summable over arbitrarily
small output/input ratios, with constants independent of the input scale.
This is a budget for the band kernels, not a claim that these overlapping
cutoffs already form a partition of unity or reconstruct the full pressure.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget

open MeasureTheory PressureLowOutputCutoff PressureLowOutputScaledKernel
open scoped SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

def dyadicParameter (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)

theorem dyadicParameter_mem (n : ℕ) : dyadicParameter n ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  constructor
  · unfold dyadicParameter; positivity
  · rw [dyadicParameter, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) : (1 / 2 : ℝ) ^ n ≤ 1) (by norm_num)).trans_eq (by ring)

theorem ratio_dyadicParameter (n : ℕ) :
    ratio (dyadicParameter n) = (1 / 256 : ℝ) * (1 / 2) ^ n := by
  rw [ratio, dyadicParameter, pow_succ]
  ring

theorem hasSum_ratio : HasSum (fun n ↦ ratio (dyadicParameter n)) (1 / 128 : ℝ) := by
  simpa only [ratio_dyadicParameter, show (1 / 256 : ℝ) * 2 = 1 / 128 by norm_num]
    using hasSum_geometric_two.mul_left (1 / 256 : ℝ)

theorem hasSum_ratio_sq : HasSum (fun n ↦ (ratio (dyadicParameter n)) ^ 2) (1 / 49152 : ℝ) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (1 / 65536 : ℝ)
  have he (n : ℕ) : (ratio (dyadicParameter n)) ^ 2 = (1 / 65536 : ℝ) * (1 / 4) ^ n := by
    rw [ratio_dyadicParameter, mul_pow, pow_right_comm]
    norm_num
  simp_rw [he]
  convert! h using 1
  norm_num

def dyadicKernel (N : ℝ) (hN : 0 < N) (e : R3) (i j l : Fin 3) (n : ℕ) : 𝓢(E6, ℂ) :=
  scaledKernel N hN (dyadicParameter n, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i

theorem exists_uniform_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      Summable (fun n ↦ ∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) ∧
      (∑' n, ∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_mass
  refine ⟨C / 49152, div_nonneg hC (by norm_num), ?_⟩
  intro N hN e he i j l
  have hsum := hasSum_ratio_sq.mul_right C
  have hle (n : ℕ) : (∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) ≤
      (ratio (dyadicParameter n)) ^ 2 * C := hb N hN _ (dyadicParameter_mem n) e he i j l
  have hs : Summable (fun n ↦ ∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) :=
    Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun x ↦ norm_nonneg _)) hle hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at ht
  exact ht.trans_eq (by ring)

theorem exists_uniform_firstMoment_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      Summable (fun n ↦ ∫ x : E6, ‖x‖ * ‖dyadicKernel N hN e i j l n x‖) ∧
      (∑' n, ∫ x : E6, ‖x‖ * ‖dyadicKernel N hN e i j l n x‖) ≤ C / N := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_firstMoment
  refine ⟨C / 128, div_nonneg hC (by norm_num), ?_⟩
  intro N hN e he i j l
  have hsum := hasSum_ratio.mul_right (C / N)
  have hle (n : ℕ) : (∫ x : E6, ‖x‖ * ‖dyadicKernel N hN e i j l n x‖) ≤
      ratio (dyadicParameter n) * (C / N) := by
    exact (hb N hN _ (dyadicParameter_mem n) e he i j l).trans_eq (by ring)
  have hs : Summable (fun n ↦ ∫ x : E6, ‖x‖ * ‖dyadicKernel N hN e i j l n x‖) :=
    Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun x ↦ by positivity)) hle hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at ht
  exact ht.trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputDyadicBudget
