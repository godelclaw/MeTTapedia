import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalKernel

/-!
# Physical kernels for coherent pressure longitudinal factors

The factored kernel is transported to the original two-input coordinates
and dilated to any positive input scale. Its mass is bounded by a constant
times the output/input ratio; its first moment is bounded by a constant
divided by the input scale. The Fourier identity retains the normalized
longitudinal input factor explicitly. No divergence-free assumption on
localized fields is made.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePhysicalKernel

open MeasureTheory Mettapedia.Analysis.SchwartzLinearChange
open Mettapedia.Analysis.SchwartzDilation
open PressureLowOutputCutoff (ratio receiver)
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputChange PressureLowOutputCoordinates
open PressureDyadicPhysicalKernel (physicalCutoff)
open PressureCoherentDivergenceKernel
open scoped FourierTransform SchwartzMap RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def physicalKernel (a : A) (i : Fin 3) : 𝓢(E6, ℂ) :=
  if h : ratio a.1 = 0 then 0 else
    pullback (spatialChange (ratio a.1) h) (retainedKernel a i)

theorem pressure_eq_fourier_physicalKernel_mul (a : A) (i : Fin 3) (ξ : E6) :
    ((physicalCutoff a.1 ξ *
        CoherentPressurePair.tiltPair a.2 (pairEquiv ξ).1 (pairEquiv ξ).2 a.2 a.2 i : ℝ) : ℂ) =
      (𝓕 (physicalKernel a i)) ξ *
        ((⟪(pairEquiv ξ).1, a.2⟫ + ⟪(pairEquiv ξ).2, a.2⟫ : ℝ) : ℂ) := by
  by_cases hr : ratio a.1 = 0
  · simp [physicalKernel, physicalCutoff, hr]
  · rw [physicalKernel, dif_neg hr, fourier_pullback, inverse_adjoint_eq_frequencyChange]
    have h := retained_pressure_eq_fourier_mul a i (frequencyChange (ratio a.1) ξ)
    simpa only [frequencyChange, pairEquiv.apply_symm_apply, receiver, smul_smul,
      mul_inv_cancel₀ hr, one_smul, add_sub_cancel_left,
      PressureDyadicSymbol.retained, physicalCutoff] using h

theorem mass_physicalKernel (a : A) (i : Fin 3) :
    (∫ x : E6, ‖physicalKernel a i x‖) = ∫ x : E6, ‖retainedKernel a i x‖ := by
  by_cases hr : ratio a.1 = 0
  · simp [physicalKernel, retainedKernel, hr]
  · rw [physicalKernel, dif_neg hr, mass_pullback]

theorem exists_uniform_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i : Fin 3, (∫ x : E6, ‖physicalKernel (t, e) i x‖) ≤ ratio t * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_retained_moment 0
  refine ⟨C, hC, fun t ht e he i ↦ ?_⟩
  rw [mass_physicalKernel]
  simpa using hb t ht e he i

theorem exists_uniform_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i : Fin 3, (∫ x : E6, ‖x‖ * ‖physicalKernel (t, e) i x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_retained_moment 1
  refine ⟨3 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t ht e he i
  have hr0 : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  by_cases hr : ratio t = 0
  · simpa [physicalKernel, hr] using mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) hC
  · have hrp : 0 < ratio t := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hhi : ratio t ≤ 1 := by unfold ratio; linarith [ht.2]
    rw [physicalKernel, dif_neg hr]
    have h := moment_pullback_le (spatialChange (ratio t) hr) (retainedKernel (t, e) i) 1
    simp only [pow_one] at h
    calc
      _ ≤ ‖(spatialChange (ratio t) hr).symm.toContinuousLinearMap‖ *
          ∫ x : E6, ‖x‖ * ‖retainedKernel (t, e) i x‖ := h
      _ ≤ (3 / ratio t) * (ratio t * C) := by
        apply mul_le_mul (opNorm_spatialChange_symm_le (ratio t) hrp hhi)
        · simpa using hb t ht e he i
        · exact integral_nonneg (fun x ↦ by positivity)
        · positivity
      _ = 3 * C := by field_simp

def scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (i : Fin 3) : 𝓢(E6, ℂ) :=
  dilate N hN.ne' (physicalKernel a i)

theorem pressure_eq_fourier_scaledKernel_mul
    (N : ℝ) (hN : 0 < N) (a : A) (i : Fin 3) (ξ : E6) :
    ((physicalCutoff a.1 (N⁻¹ • ξ) *
        CoherentPressurePair.tiltPair a.2 (pairEquiv ξ).1 (pairEquiv ξ).2 a.2 a.2 i : ℝ) : ℂ) =
      (𝓕 (scaledKernel N hN a i)) ξ *
        ((N⁻¹ * (⟪(pairEquiv ξ).1, a.2⟫ + ⟪(pairEquiv ξ).2, a.2⟫) : ℝ) : ℂ) := by
  rw [scaledKernel, fourier_dilate]
  have h := pressure_eq_fourier_physicalKernel_mul a i (N⁻¹ • ξ)
  simpa only [map_smul, Prod.smul_fst, Prod.smul_snd,
    tiltPair_smul_frequencies N⁻¹ (inv_ne_zero hN.ne'), real_inner_smul_left,
    ← mul_add] using h

theorem exists_uniform_scaled_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i : Fin 3,
      (∫ x : E6, ‖scaledKernel N hN (t, e) i x‖) ≤ ratio t * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mass
  refine ⟨C, hC, fun N hN t ht e he i ↦ ?_⟩
  rw [scaledKernel, mass_dilate]
  exact hb t ht e he i

theorem exists_uniform_scaled_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i : Fin 3,
      (∫ x : E6, ‖x‖ * ‖scaledKernel N hN (t, e) i x‖) ≤ C / N := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_firstMoment
  refine ⟨C, hC, fun N hN t ht e he i ↦ ?_⟩
  have h := moment_dilate N hN.ne' (physicalKernel (t, e) i) 1
  simp only [pow_one, abs_of_pos hN] at h
  rw [scaledKernel, h]
  calc
    _ ≤ N⁻¹ * C := mul_le_mul_of_nonneg_left (hb t ht e he i) (inv_nonneg.mpr hN.le)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePhysicalKernel
