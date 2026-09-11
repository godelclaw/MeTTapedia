import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputChange
import Mettapedia.Analysis.SchwartzDilation

/-!
# Physical exact-partition pressure kernels

The exact-partition symbols are transferred to the original two-input
coordinates and any positive input scale. Their actual inverse Fourier
kernels have mass of order ratio squared and first moment of order
ratio divided by input scale. Constants are uniform over all coordinate
entries and unit frozen directions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel

open MeasureTheory Mettapedia.Analysis.SchwartzLinearChange
open Mettapedia.Analysis.SchwartzDilation Mettapedia.Analysis.DyadicAnnulus
open PressureLowOutputCutoff (ratio parameterCutoff receiver)
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputChange PressureLowOutputCoordinates
open PressureDyadicKernel
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def physicalKernel (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  if h : ratio a.1 = 0 then 0 else
    pullback (spatialChange (ratio a.1) h) (retainedKernel a w v i)

def physicalCutoff (t : ℝ) (ξ : E6) : ℝ :=
  parameterCutoff t * normalizedCutoff (pairEquiv ξ).1 *
    normalizedCutoff ((ratio t)⁻¹ • ((pairEquiv ξ).1 + (pairEquiv ξ).2))

theorem fourier_physicalKernel (a : A) (w v : R3) (i : Fin 3) (ξ : E6) :
    (𝓕 (physicalKernel a w v i)) ξ =
      ((physicalCutoff a.1 ξ *
        CoherentPressurePair.tiltPair a.2 (pairEquiv ξ).1 (pairEquiv ξ).2 w v i : ℝ) : ℂ) := by
  by_cases hr : ratio a.1 = 0
  · simp [physicalKernel, physicalCutoff, hr]
  · rw [physicalKernel, dif_neg hr, fourier_pullback, inverse_adjoint_eq_frequencyChange,
      fourier_retainedKernel]
    simp only [frequencyChange, pairEquiv.apply_symm_apply, receiver, smul_smul,
      mul_inv_cancel₀ hr, one_smul, add_sub_cancel_left]
    rfl

theorem mass_physicalKernel (a : A) (w v : R3) (i : Fin 3) :
    (∫ x : E6, ‖physicalKernel a w v i x‖) = ∫ x : E6, ‖retainedKernel a w v i x‖ := by
  by_cases hr : ratio a.1 = 0
  · simp [physicalKernel, retainedKernel, hr]
  · rw [physicalKernel, dif_neg hr, mass_pullback]

theorem exists_uniform_basis_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i j l : Fin 3,
      (∫ x : E6, ‖physicalKernel (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_moment 0
  refine ⟨C, hC, fun t ht e he i j l ↦ ?_⟩
  rw [mass_physicalKernel]
  simpa using hb t ht e he i j l

theorem exists_uniform_basis_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ * ‖physicalKernel (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ ratio t * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_moment 1
  refine ⟨3 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t ht e he i j l
  have hr0 : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  by_cases hr : ratio t = 0
  · simp [physicalKernel, hr]
  · have hrp : 0 < ratio t := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hhi : ratio t ≤ 1 := by unfold ratio; linarith [ht.2]
    rw [physicalKernel, dif_neg hr]
    have h := moment_pullback_le (spatialChange (ratio t) hr) (retainedKernel (t, e)
      (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i) 1
    simp only [pow_one] at h
    calc
      _ ≤ ‖(spatialChange (ratio t) hr).symm.toContinuousLinearMap‖ *
          ∫ x : E6, ‖x‖ * ‖retainedKernel (t, e)
            (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ := h
      _ ≤ (3 / ratio t) * ((ratio t) ^ 2 * C) := by
        apply mul_le_mul (opNorm_spatialChange_symm_le (ratio t) hrp hhi)
        · simpa using hb t ht e he i j l
        · exact integral_nonneg (fun x ↦ by positivity)
        · positivity
      _ = ratio t * (3 * C) := by field_simp

def scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  dilate N hN.ne' (physicalKernel a w v i)

theorem fourier_scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) (ξ : E6) :
    (𝓕 (scaledKernel N hN a w v i)) ξ =
      ((physicalCutoff a.1 (N⁻¹ • ξ) *
        CoherentPressurePair.tiltPair a.2 (pairEquiv ξ).1 (pairEquiv ξ).2 w v i : ℝ) : ℂ) := by
  rw [scaledKernel, fourier_dilate, fourier_physicalKernel]
  simp only [map_smul, Prod.smul_fst, Prod.smul_snd,
    tiltPair_smul_frequencies N⁻¹ (inv_ne_zero hN.ne')]

theorem exists_uniform_scaled_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖scaledKernel N hN (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_mass
  refine ⟨C, hC, fun N hN t ht e he i j l ↦ ?_⟩
  rw [scaledKernel, mass_dilate]
  exact hb t ht e he i j l

theorem exists_uniform_scaled_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ * ‖scaledKernel N hN (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t / N) * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_basis_firstMoment
  refine ⟨C, hC, fun N hN t ht e he i j l ↦ ?_⟩
  have h := moment_dilate N hN.ne' (physicalKernel (t, e)
    (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i) 1
  simp only [pow_one, abs_of_pos hN] at h
  rw [scaledKernel, h]
  calc
    _ ≤ N⁻¹ * (ratio t * C) := mul_le_mul_of_nonneg_left (hb t ht e he i j l) (inv_nonneg.mpr hN.le)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalKernel
