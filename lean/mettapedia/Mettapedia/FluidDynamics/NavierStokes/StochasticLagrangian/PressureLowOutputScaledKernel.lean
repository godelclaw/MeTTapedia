import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputPhysicalKernel
import Mettapedia.Analysis.SchwartzDilation

/-!
# Low-output pressure kernels at arbitrary input scale

The common input scale does not alter pressure-pair amplitudes. It leaves
kernel mass unchanged and divides the first spatial moment by that scale.
The constants are uniform in the input scale, output/input ratio, unit
frozen direction, and all coordinate entries.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel

open MeasureTheory Mettapedia.Analysis.SchwartzDilation
open PressureLowOutputCutoff PressureLowOutputSymbol PressureLowOutputCoordinates
open PressureLowOutputPhysicalKernel
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  dilate N hN.ne' (physicalKernel a w v i)

theorem fourier_scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) (ξ : E6) :
    (𝓕 (scaledKernel N hN a w v i)) ξ =
      ((physicalCutoff a.1 (N⁻¹ • ξ) *
        CoherentPressurePair.tiltPair a.2 (pairEquiv ξ).1 (pairEquiv ξ).2 w v i : ℝ) : ℂ) := by
  rw [scaledKernel, fourier_dilate, fourier_physicalKernel]
  simp only [map_smul, Prod.smul_fst, Prod.smul_snd,
    tiltPair_smul_frequencies N⁻¹ (inv_ne_zero hN.ne')]

theorem mass_scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) :
    (∫ x : E6, ‖scaledKernel N hN a w v i x‖) = ∫ x : E6, ‖physicalKernel a w v i x‖ := by
  rw [scaledKernel, mass_dilate]

theorem firstMoment_scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (w v : R3) (i : Fin 3) :
    (∫ x : E6, ‖x‖ * ‖scaledKernel N hN a w v i x‖) =
      N⁻¹ * ∫ x : E6, ‖x‖ * ‖physicalKernel a w v i x‖ := by
  simpa [scaledKernel, abs_of_pos hN] using moment_dilate N hN.ne' (physicalKernel a w v i) 1

theorem exists_uniform_basis_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖scaledKernel N hN (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := PressureLowOutputPhysicalKernel.exists_uniform_basis_mass
  refine ⟨C, hC, fun N hN t ht e he i j l ↦ ?_⟩
  rw [mass_scaledKernel]
  exact hb t ht e he i j l

theorem exists_uniform_basis_firstMoment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ * ‖scaledKernel N hN (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t / N) * C := by
  obtain ⟨C, hC, hb⟩ := PressureLowOutputPhysicalKernel.exists_uniform_basis_firstMoment
  refine ⟨C, hC, fun N hN t ht e he i j l ↦ ?_⟩
  rw [firstMoment_scaledKernel]
  calc
    _ ≤ N⁻¹ * (ratio t * C) := mul_le_mul_of_nonneg_left (hb t ht e he i j l) (inv_nonneg.mpr hN.le)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputScaledKernel
