import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureL2FourierReconstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelWeakFourier

/-!
# Coherent channel identities for the actual weak-input fields

The first input-coordinate channel, multiplied by `2 pi i N`, is the
undifferentiated kernel acting on the actual weak coordinate derivative.
The equality holds almost everywhere in physical space, not only for
Fourier coefficients. The derivative-energy cost remains explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer

open MeasureTheory PressureKernelAction PressureL2KernelAction
open PressureCoherentChannelPeriodization PeriodicVectorWeakDerivative
open FourierPressureTraceSymbol (complexifyVector)
open PancakeFourierMaterialPaths (torusPoint)
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem first_channel_eq_ae (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ f (torusPoint r))) (g : C(T3, C3)) :
    (fun x ↦ (unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.first j)) (fun y ↦ complexifyVector (f y)) g x) =ᵐ[volume]
      kernelAction (periodicKernel N hN t e .undifferentiated)
        (fun y ↦ complexifyVector (coordinateRate f j y)) g := by
  exact PressureL2FourierReconstruction.smul_kernelAction_eq_ae _ _
    (integrable_periodicKernel N hN t e (.first j))
    (integrable_periodicKernel N hN t e .undifferentiated) _ _
    (memLp_complexify f (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
    (memLp_complexify _ (memLp_coordinateRate f j hf hfL)) g _
    (PressureCoherentChannelWeakFourier.first_channel_weakDerivative N hN t e j f hf hfL)

theorem first_channel_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ f (torusPoint r))) (g : C(T3, C3)) :
    ‖unitTorusDerivativePhase * (N : ℂ)‖ ^ 2 *
      (∫ x : T3, ‖kernelAction (periodicKernel N hN t e (.first j))
        (fun y ↦ complexifyVector (f y)) g x‖ ^ 2) ≤
      (∫ q : T6, ‖periodicKernel N hN t e .undifferentiated q‖) ^ 2 * ‖g‖ ^ 2 *
        ∫ x : T3, ‖coordinateRate f j x‖ ^ 2 := by
  calc
    _ = ∫ x : T3, ‖(unitTorusDerivativePhase * (N : ℂ)) •
        kernelAction (periodicKernel N hN t e (.first j))
          (fun y ↦ complexifyVector (f y)) g x‖ ^ 2 := by
      simp only [norm_smul, mul_pow, integral_const_mul]
    _ = ∫ x : T3, ‖kernelAction (periodicKernel N hN t e .undifferentiated)
        (fun y ↦ complexifyVector (coordinateRate f j y)) g x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [first_channel_eq_ae N hN t e j f hf hfL g] with x hx
      rw [hx]
    _ ≤ _ := by
      simpa only [FourierPressureTraceSymbol.norm_complexifyVector] using
        (kernelAction_memLp_two_and_energy_le _
          (integrable_periodicKernel N hN t e .undifferentiated) _ g
          (memLp_complexify _ (memLp_coordinateRate f j hf hfL))).2.2

/-- The ratio and inverse-input-scale gains survive in the actual field estimate. -/
theorem exists_uniform_first_channel_derivative_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ e : R3, ‖e‖ = 1 → ∀ j : Fin 3, ∀ f : T3 → R3, Continuous f →
      LocallyLipschitz (fun r : Fin 3 → ℝ ↦ f (torusPoint r)) → ∀ g : C(T3, C3),
        (∫ x : T3, ‖kernelAction (periodicKernel N hN t e (.first j))
          (fun y ↦ complexifyVector (f y)) g x‖ ^ 2) ≤
          C * PressureLowOutputCutoff.ratio t ^ 2 / (2 * Real.pi * N) ^ 2 * ‖g‖ ^ 2 *
            ∫ x : T3, ‖coordinateRate f j x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_coherent_energy_bound
  refine ⟨C, hC, fun N hN t ht e he j f hf hfL g ↦ ?_⟩
  have hz : ‖unitTorusDerivativePhase * (N : ℂ)‖ = 2 * Real.pi * N := by
    rw [norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have henergy : (2 * Real.pi * N) ^ 2 *
      (∫ x : T3, ‖kernelAction (periodicKernel N hN t e (.first j))
        (fun y ↦ complexifyVector (f y)) g x‖ ^ 2) =
      ∫ x : T3, ‖kernelAction (periodicKernel N hN t e .undifferentiated)
        (fun y ↦ complexifyVector (coordinateRate f j y)) g x‖ ^ 2 := by
    calc
      _ = ∫ x : T3, ‖(unitTorusDerivativePhase * (N : ℂ)) •
          kernelAction (periodicKernel N hN t e (.first j))
            (fun y ↦ complexifyVector (f y)) g x‖ ^ 2 := by
        simp only [norm_smul, mul_pow, integral_const_mul, hz]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [first_channel_eq_ae N hN t e j f hf hfL g] with x hx
        rw [hx]
  have h := hbound N hN t ht e he .undifferentiated
    (fun y ↦ complexifyVector (coordinateRate f j y)) g
    (memLp_complexify _ (memLp_coordinateRate f j hf hfL))
  rw [← henergy] at h
  simp only [FourierPressureTraceSymbol.norm_complexifyVector] at h
  have hd : 0 < (2 * Real.pi * N) ^ 2 := by positivity
  calc
    _ ≤ (C * PressureLowOutputCutoff.ratio t ^ 2 * ‖g‖ ^ 2 *
        ∫ x : T3, ‖coordinateRate f j x‖ ^ 2) / (2 * Real.pi * N) ^ 2 :=
      (le_div_iff₀ hd).mpr (by simpa only [mul_comm _ ((2 * Real.pi * N) ^ 2)] using h)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer
