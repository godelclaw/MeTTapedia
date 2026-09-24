import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputChange
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputKernel

/-!
# Physical low-output pressure kernels

The Jacobian-normalized inverse coordinate change retains quadratic smallness
in kernel mass and linear smallness in the first spatial moment. The Fourier
transform is the actual pressure-pair entry on the retained original input
frequencies. The singular zero-ratio coordinate change is replaced by the
zero pressure kernel, consistently with its symbol.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel

open MeasureTheory Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SmoothAnnulus
open PressureLowOutputCutoff PressureLowOutputSymbol PressureLowOutputChange PressureLowOutputKernel
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def physicalKernel (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  if h : ratio a.1 = 0 then 0 else
    pullback (spatialChange (ratio a.1) h) (retainedKernel a w v i)

def physicalCutoff (t : ℝ) (ξ : E6) : ℝ :=
  parameterCutoff t * cutoff (pairEquiv ξ).1 *
    cutoff ((ratio t)⁻¹ • ((pairEquiv ξ).1 + (pairEquiv ξ).2))

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

@[simp] theorem physicalKernel_zero (e w v : R3) (i : Fin 3) :
    physicalKernel (0, e) w v i = 0 := by simp [physicalKernel, ratio]

theorem mass_physicalKernel (a : A) (w v : R3) (i : Fin 3) :
    (∫ x : E6, ‖physicalKernel a w v i x‖) =
      ∫ x : E6, ‖retainedKernel a w v i x‖ := by
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

theorem firstMoment_physicalKernel_le (t : ℝ) (hr : 0 < ratio t) (hhi : ratio t ≤ 1)
    (e w v : R3) (i : Fin 3) :
    (∫ x : E6, ‖x‖ * ‖physicalKernel (t, e) w v i x‖) ≤
      (3 / ratio t) * ∫ x : E6, ‖x‖ * ‖retainedKernel (t, e) w v i x‖ := by
  rw [physicalKernel, dif_neg hr.ne']
  have h := moment_pullback_le (spatialChange (ratio t) hr.ne') (retainedKernel (t, e) w v i) 1
  simp only [pow_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (opNorm_spatialChange_symm_le (ratio t) hr hhi) (integral_nonneg (fun x ↦ by positivity)))

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
    calc
      _ ≤ (3 / ratio t) * ∫ x : E6, ‖x‖ * ‖retainedKernel (t, e)
          (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖ :=
        firstMoment_physicalKernel_le t hrp hhi e _ _ i
      _ ≤ (3 / ratio t) * ((ratio t) ^ 2 * C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using hb t ht e he i j l
      _ = ratio t * (3 * C) := by field_simp

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPhysicalKernel
