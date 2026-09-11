import Mettapedia.Analysis.SchwartzBilinearKernel
import Mettapedia.Analysis.BilinearCoefficientSums
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureOperatorCoordinates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPartition

/-!
# Complex-bilinear exact-partition pressure kernels

Scalar physical kernels assemble into the actual complex-bilinear pressure
operator on lattice frequencies. Mass and first-moment bounds retain their
quadratic and linear output-ratio gains, with the finite coordinate cost
explicit and independent of frequency scale.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel

open MeasureTheory Mettapedia.Analysis.EuclideanBilinearCoordinates
open Mettapedia.Analysis.SchwartzBilinearKernel
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator FourierPressureCommutator
open PressureLowOutputCutoff (ratio)
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel PressureOperatorCoordinates PressureBilinearOperator
open PressureLowOutputDyadicBudget (dyadicParameter dyadicParameter_mem hasSum_ratio hasSum_ratio_sq)
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

def operatorKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) : 𝓢(E6, Op) :=
  assemble (fun i j l : Fin 3 ↦ scaledKernel N hN (t, e)
    (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i)

theorem fourier_operatorKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) :
    (𝓕 (operatorKernel N hN t e)) (pairEquiv.symm (realFrequency k, realFrequency p)) =
      (physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
        pressurePairOperator e he k p := by
  rw [operatorKernel, fourier_assemble]
  have hentry : (fun i j l : Fin 3 ↦
      (𝓕 (scaledKernel N hN (t, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i))
        (pairEquiv.symm (realFrequency k, realFrequency p))) =
      entry ((physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
        pressurePairOperator e he k p) := by
    funext i j l
    rw [fourier_scaledKernel]
    simp only [pairEquiv.apply_symm_apply, Complex.ofReal_mul]
    rw [← entry_pressurePairOperator e he k p]
    simp [Mettapedia.Analysis.EuclideanBilinearCoordinates.entry]
  rw [hentry, reconstruct_entry]

theorem moment_operatorKernel_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (m : ℕ) :
    (∫ x : E6, ‖x‖ ^ m * ‖operatorKernel N hN t e x‖) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ∫ x : E6, ‖x‖ ^ m * ‖scaledKernel N hN (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ :=
  moment_assemble_le _ m

theorem hasSum_fourier_operatorKernel (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (hsmall : ‖realFrequency k + realFrequency p‖ ≤ N / 256) :
    HasSum (fun n : ℕ ↦ (𝓕 (operatorKernel N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) e))
      (pairEquiv.symm (realFrequency k, realFrequency p)))
      ((Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
        pressurePairOperator e he k p) := by
  let B : Op := (Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
    pressurePairOperator e he k p
  have hentry (i j l : Fin 3) :
      HasSum (fun n : ℕ ↦ (𝓕 (scaledKernel N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i))
        (pairEquiv.symm (realFrequency k, realFrequency p))) (entry B i j l) := by
    have h := PressureDyadicPartition.hasSum_fourier_scaledKernel N hN e
      (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i
      (pairEquiv.symm (realFrequency k, realFrequency p)) (by simpa using hsmall)
    simp only [pairEquiv.apply_symm_apply, Complex.ofReal_mul] at h
    rw [← entry_pressurePairOperator e he k p] at h
    simpa [B, Mettapedia.Analysis.EuclideanBilinearCoordinates.entry] using h
  have h := hasSum_reconstruct _ (entry B) hentry
  simpa only [operatorKernel, fourier_assemble, reconstruct_entry] using h

theorem exists_uniform_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖operatorKernel N hN t e x‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicPhysicalKernel.exists_uniform_scaled_mass
  refine ⟨27 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro N hN t ht e he
  have h := moment_operatorKernel_le N hN t e 0
  simp only [pow_zero, one_mul] at h
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, (ratio t) ^ 2 * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact hb N hN t ht e he i j l
    _ = _ := by simp; ring

theorem exists_uniform_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖x‖ * ‖operatorKernel N hN t e x‖) ≤ (ratio t / N) * C := by
  obtain ⟨C, hC, hb⟩ := PressureDyadicPhysicalKernel.exists_uniform_scaled_firstMoment
  refine ⟨27 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro N hN t ht e he
  have h := moment_operatorKernel_le N hN t e 1
  simp only [pow_one] at h
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, (ratio t / N) * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact hb N hN t ht e he i j l
    _ = _ := by simp; ring

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


end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel
