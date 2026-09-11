import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputDyadicBudget

/-!
# Exact low-output reconstruction and summable physical costs

The output bands sum to one for nonzero output of norm at most one input
scale divided by 256. Reconstruction concerns the actual corrected pressure
symbol. Separately, the actual new kernels have summable mass and first
moment. No bound for the other frequency sectors is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition

open MeasureTheory Mettapedia.Analysis.DyadicAnnulus
open PressureLowOutputCutoff (ratio parameterCutoff_eq_one)
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputDyadicBudget (dyadicParameter dyadicParameter_mem ratio_dyadicParameter
  hasSum_ratio hasSum_ratio_sq)
open PressureDyadicPhysicalKernel
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

theorem inverse_ratio_dyadicParameter (n : ℕ) :
    (ratio (dyadicParameter n))⁻¹ = (2 : ℝ) ^ n * 256 := by
  rw [ratio_dyadicParameter]
  simp [mul_inv_rev, inv_pow]

theorem physicalCutoff_dyadicParameter (n : ℕ) (ξ : E6) :
    physicalCutoff (dyadicParameter n) ξ = normalizedCutoff (pairEquiv ξ).1 *
      normalizedCutoff ((2 : ℝ) ^ n • ((256 : ℝ) • ((pairEquiv ξ).1 + (pairEquiv ξ).2))) := by
  rw [physicalCutoff, parameterCutoff_eq_one _ (dyadicParameter_mem n), one_mul,
    inverse_ratio_dyadicParameter, mul_smul]

theorem summable_physicalCutoff (ξ : E6) :
    Summable (fun n : ℕ ↦ physicalCutoff (dyadicParameter n) ξ) := by
  simpa only [physicalCutoff_dyadicParameter] using
    (summable_normalizedCutoff_nat ((256 : ℝ) • ((pairEquiv ξ).1 + (pairEquiv ξ).2))).mul_left
      (normalizedCutoff (pairEquiv ξ).1)

theorem tsum_physicalCutoff (ξ : E6)
    (hq : (pairEquiv ξ).1 + (pairEquiv ξ).2 ≠ 0)
    (hsmall : ‖(pairEquiv ξ).1 + (pairEquiv ξ).2‖ ≤ 1 / 256) :
    ∑' n : ℕ, physicalCutoff (dyadicParameter n) ξ = normalizedCutoff (pairEquiv ξ).1 := by
  have hnz : (256 : ℝ) • ((pairEquiv ξ).1 + (pairEquiv ξ).2) ≠ 0 := smul_ne_zero (by norm_num) hq
  have hn : ‖(256 : ℝ) • ((pairEquiv ξ).1 + (pairEquiv ξ).2)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 256)]
    linarith
  simp only [physicalCutoff_dyadicParameter, tsum_mul_left,
    tsum_normalizedCutoff_nat _ hnz hn, mul_one]

theorem tsum_scaled_physicalCutoff (N : ℝ) (hN : 0 < N) (ξ : E6)
    (hq : (pairEquiv ξ).1 + (pairEquiv ξ).2 ≠ 0)
    (hsmall : ‖(pairEquiv ξ).1 + (pairEquiv ξ).2‖ ≤ N / 256) :
    ∑' n : ℕ, physicalCutoff (dyadicParameter n) (N⁻¹ • ξ) =
      normalizedCutoff (N⁻¹ • (pairEquiv ξ).1) := by
  have he : (pairEquiv (N⁻¹ • ξ)).1 + (pairEquiv (N⁻¹ • ξ)).2 =
      N⁻¹ • ((pairEquiv ξ).1 + (pairEquiv ξ).2) := by simp [smul_add]
  have hnz : (pairEquiv (N⁻¹ • ξ)).1 + (pairEquiv (N⁻¹ • ξ)).2 ≠ 0 := by
    rw [he]
    exact smul_ne_zero (inv_ne_zero hN.ne') hq
  have hn : ‖(pairEquiv (N⁻¹ • ξ)).1 + (pairEquiv (N⁻¹ • ξ)).2‖ ≤ 1 / 256 := by
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hN.le)]
    calc
      _ ≤ N⁻¹ * (N / 256) := mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hN.le)
      _ = _ := by field_simp
  simpa only [map_smul, Prod.smul_fst] using tsum_physicalCutoff (N⁻¹ • ξ) hnz hn

/-- The actual Fourier kernels reconstruct the retained pressure coefficient,
including exact zero output. No unit-direction hypothesis is needed for the identity. -/
theorem hasSum_fourier_scaledKernel (N : ℝ) (hN : 0 < N) (e w v : R3) (i : Fin 3) (ξ : E6)
    (hsmall : ‖(pairEquiv ξ).1 + (pairEquiv ξ).2‖ ≤ N / 256) :
    HasSum (fun n : ℕ ↦ (𝓕 (scaledKernel N hN (dyadicParameter n, e) w v i)) ξ)
      (((normalizedCutoff (N⁻¹ • (pairEquiv ξ).1)) *
        CoherentPressurePair.tiltPair e (pairEquiv ξ).1 (pairEquiv ξ).2 w v i : ℝ) : ℂ) := by
  simp_rw [fourier_scaledKernel]
  by_cases hq : (pairEquiv ξ).1 + (pairEquiv ξ).2 = 0
  · simp [CoherentPressurePair.tiltPair, hq, PressureTiltSymbol.tiltSymbol_zero]
  · have h := (summable_physicalCutoff (N⁻¹ • ξ)).hasSum
    rw [tsum_scaled_physicalCutoff N hN ξ hq hsmall] at h
    exact Complex.hasSum_ofReal.mpr (h.mul_right
      (CoherentPressurePair.tiltPair e (pairEquiv ξ).1 (pairEquiv ξ).2 w v i))

def dyadicKernel (N : ℝ) (hN : 0 < N) (e : R3) (i j l : Fin 3) (n : ℕ) : 𝓢(E6, ℂ) :=
  scaledKernel N hN (dyadicParameter n, e) (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i

theorem exists_uniform_mass_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      Summable (fun n ↦ ∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) ∧
      (∑' n, ∫ x : E6, ‖dyadicKernel N hN e i j l n x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_scaled_mass
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
  obtain ⟨C, hC, hb⟩ := exists_uniform_scaled_firstMoment
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

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPartition
