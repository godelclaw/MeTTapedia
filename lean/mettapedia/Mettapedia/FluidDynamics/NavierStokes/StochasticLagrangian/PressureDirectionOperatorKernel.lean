import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairPeriodizationLinearity

/-! Direction-gap gains survive bilinear assembly and actual periodization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel

open MeasureTheory Mettapedia.Analysis.SchwartzBilinearKernel
open PressureDyadicPhysicalKernel PressureDyadicOperatorKernel PressureDyadicPeriodization
open FrequencyPairPeriodization FrequencyPairPeriodizationLinearity
open PressureLowOutputCutoff (ratio)
open scoped SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem moment_operatorKernel_sub_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e f : R3) (m : ℕ) :
    (∫ x : E6, ‖x‖ ^ m * ‖operatorKernel N hN t e x - operatorKernel N hN t f x‖) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x : E6, ‖x‖ ^ m *
        ‖scaledKernel N hN (t, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x -
          scaledKernel N hN (t, f) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ := by
  have h := moment_assemble_le (fun i j l : Fin 3 ↦
    scaledKernel N hN (t, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i -
    scaledKernel N hN (t, f) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i) m
  simpa only [assemble_sub, sub_apply, operatorKernel] using h

theorem exists_uniform_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 →
      (∫ x : E6, ‖operatorKernel N hN t e x - operatorKernel N hN t f x‖) ≤
        (ratio t) ^ 2 * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := PressureDirectionKernel.exists_uniform_scaled_mass
  refine ⟨27 * C, by positivity, ?_⟩
  intro N hN t ht e f he hf
  have h := moment_operatorKernel_sub_le N hN t e f 0
  simp only [pow_zero, one_mul] at h
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, (ratio t) ^ 2 * ‖e - f‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact hb N hN t ht e f he hf i j l
    _ = _ := by simp; ring

theorem exists_uniform_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 →
      (∫ x : E6, ‖x‖ * ‖operatorKernel N hN t e x - operatorKernel N hN t f x‖) ≤
        (ratio t / N) * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := PressureDirectionKernel.exists_uniform_scaled_firstMoment
  refine ⟨27 * C, by positivity, ?_⟩
  intro N hN t ht e f he hf
  have h := moment_operatorKernel_sub_le N hN t e f 1
  simp only [pow_one] at h
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, (ratio t / N) * ‖e - f‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact hb N hN t ht e f he hf i j l
    _ = _ := by simp; ring

theorem moment_periodicKernel_sub_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e f : R3) (m : ℕ) :
    (∫ q : T6, ‖q‖ ^ m * ‖periodicKernel N hN t e q - periodicKernel N hN t f q‖) ≤
      ∫ x : E6, ‖x‖ ^ m * ‖operatorKernel N hN t e x - operatorKernel N hN t f x‖ := by
  have ha := periodize_sub_ae (operatorKernel N hN t e) (operatorKernel N hN t f)
    (operatorKernel N hN t e).continuous.measurable (operatorKernel N hN t f).continuous.measurable
    (operatorKernel N hN t e).integrable (operatorKernel N hN t f).integrable
  have heq : (∫ q : T6, ‖q‖ ^ m * ‖periodicKernel N hN t e q - periodicKernel N hN t f q‖) =
      ∫ q : T6, ‖q‖ ^ m * ‖periodize (operatorKernel N hN t e - operatorKernel N hN t f) q‖ := by
    apply integral_congr_ae
    filter_upwards [ha] with q hq
    rw [show periodize (operatorKernel N hN t e - operatorKernel N hN t f) q =
      periodicKernel N hN t e q - periodicKernel N hN t f q from hq]
  rw [heq]
  exact FrequencyPairPeriodization.integral_moment_periodize_le
    (operatorKernel N hN t e - operatorKernel N hN t f) m

theorem exists_uniform_periodic_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 →
      (∫ q : T6, ‖periodicKernel N hN t e q - periodicKernel N hN t f q‖) ≤
        (ratio t) ^ 2 * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mass
  refine ⟨C, hC, ?_⟩
  intro N hN t ht e f he hf
  have h := moment_periodicKernel_sub_le N hN t e f 0
  simp only [pow_zero, one_mul] at h
  exact h.trans (hb N hN t ht e f he hf)

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel
