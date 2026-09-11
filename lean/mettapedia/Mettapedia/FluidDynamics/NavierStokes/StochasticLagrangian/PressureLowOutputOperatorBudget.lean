import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputOperatorKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputDyadicBudget

/-!
# Dyadic budgets for complex-bilinear pressure operators

The physical operator-norm masses and first moments are summable over the
low-output bands. The constants are uniform in the common input scale and
unit frozen direction. No decomposition or time-integrated NS estimate is
assumed or concluded here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorBudget

open MeasureTheory PressureLowOutputCutoff PressureLowOutputDyadicBudget PressureLowOutputOperatorKernel
open scoped SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup

theorem exists_uniform_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n ↦ ∫ x : E6, ‖operatorKernel N hN (dyadicParameter n) e x‖) ∧
      (∑' n, ∫ x : E6, ‖operatorKernel N hN (dyadicParameter n) e x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mass
  refine ⟨C / 49152, div_nonneg hC (by norm_num), ?_⟩
  intro N hN e he
  have hsum := hasSum_ratio_sq.mul_right C
  have hle (n : ℕ) : (∫ x : E6, ‖operatorKernel N hN (dyadicParameter n) e x‖) ≤
      (ratio (dyadicParameter n)) ^ 2 * C := hb N hN _ (dyadicParameter_mem n) e he
  have hs := Summable.of_nonneg_of_le
    (fun n ↦ integral_nonneg (fun x ↦ norm_nonneg (operatorKernel N hN (dyadicParameter n) e x)))
    hle hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at ht
  exact ht.trans_eq (by ring)

theorem exists_uniform_firstMoment_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n ↦ ∫ x : E6, ‖x‖ * ‖operatorKernel N hN (dyadicParameter n) e x‖) ∧
      (∑' n, ∫ x : E6, ‖x‖ * ‖operatorKernel N hN (dyadicParameter n) e x‖) ≤ C / N := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_firstMoment
  refine ⟨C / 128, div_nonneg hC (by norm_num), ?_⟩
  intro N hN e he
  have hsum := hasSum_ratio.mul_right (C / N)
  have hle (n : ℕ) : (∫ x : E6, ‖x‖ * ‖operatorKernel N hN (dyadicParameter n) e x‖) ≤
      ratio (dyadicParameter n) * (C / N) :=
    (hb N hN _ (dyadicParameter_mem n) e he).trans_eq (by ring)
  have hs := Summable.of_nonneg_of_le
    (fun n ↦ integral_nonneg (fun x ↦ by positivity)) hle hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at ht
  exact ht.trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorBudget
