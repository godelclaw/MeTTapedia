import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureL2KernelAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakDivergence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentWeakFieldTransfer

/-!
# Pressure kernels applied to the actual root-vorticity weak derivative

These are physical-space Bochner integrals, with one actual weak
derivative input and one continuous root-vorticity input. Both slots
produce L² fields. The energy bound retains the kernel mass and the
actual root-field supremum; no time control of those costs is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open GaussianRootVorticity GaussianRootPartition GaussianRootWeakDivergence
open FourierPressureTraceSymbol PressureKernelAction PressureL2KernelAction
open PressureCoherentChannelPeriodization
open PressureLowOutputCutoff (ratio)

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

variable (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
variable (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers)

def rootInput : C(T3, C3) :=
  ⟨fun x ↦ complexifyVector (rootVorticity gamma chi modes u centers tau i x), by
    have h := continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp h)⟩

omit hg hu hc in
def derivativeInput (j : Fin 3) (x : T3) : C3 :=
  complexifyVector (coordinateDerivative gamma chi modes u centers tau i j x)

include hg hu hc in
theorem memLp_derivativeInput (j : Fin 3) :
    MemLp (derivativeInput gamma chi modes u centers tau i j) 2 :=
  PeriodicVectorWeakDerivative.memLp_complexify _
    (memLp_coordinateDerivative gamma hg chi modes u hu centers hc tau i j)

def firstDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) : T3 → C3 :=
  kernelAction (periodicKernel N hN t e .undifferentiated)
    (derivativeInput gamma chi modes u centers tau i j)
    (rootInput gamma hg chi modes u hu centers hc tau i)

def secondDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) : T3 → C3 :=
  kernelAction (periodicKernel N hN t e .undifferentiated)
    (rootInput gamma hg chi modes u hu centers hc tau i)
    (derivativeInput gamma chi modes u centers tau i j)

theorem ae_integrable_firstDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    ∀ᵐ x : T3, Integrable (fun q : T6 ↦ periodicKernel N hN t e .undifferentiated q
      (derivativeInput gamma chi modes u centers tau i j
        (x - PancakeBilinearPeriodization.firstTorusDisplacement q))
      (rootInput gamma hg chi modes u hu centers hc tau i
        (x - PancakeBilinearPeriodization.secondTorusDisplacement q))) :=
  (kernelAction_memLp_two_and_energy_le _ (integrable_periodicKernel N hN t e .undifferentiated)
    _ (rootInput gamma hg chi modes u hu centers hc tau i)
    (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).1

theorem ae_integrable_secondDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    ∀ᵐ x : T3, Integrable (fun q : T6 ↦ periodicKernel N hN t e .undifferentiated q
      (rootInput gamma hg chi modes u hu centers hc tau i
        (x - PancakeBilinearPeriodization.firstTorusDisplacement q))
      (derivativeInput gamma chi modes u centers tau i j
        (x - PancakeBilinearPeriodization.secondTorusDisplacement q))) :=
  (kernelAction_memLp_two_and_energy_le_right _ (integrable_periodicKernel N hN t e .undifferentiated)
    (rootInput gamma hg chi modes u hu centers hc tau i) _
    (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).1

theorem memLp_firstDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    MemLp (firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j) 2 :=
  (kernelAction_memLp_two_and_energy_le _ (integrable_periodicKernel N hN t e .undifferentiated)
    _ (rootInput gamma hg chi modes u hu centers hc tau i)
    (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).2.1

theorem memLp_secondDerivativeAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    MemLp (secondDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j) 2 :=
  (kernelAction_memLp_two_and_energy_le_right _ (integrable_periodicKernel N hN t e .undifferentiated)
    (rootInput gamma hg chi modes u hu centers hc tau i) _
    (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).2.1

theorem firstDerivativeAction_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    (∫ x : T3, ‖firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j x‖ ^ 2) ≤
      (∫ q : T6, ‖periodicKernel N hN t e .undifferentiated q‖) ^ 2 *
        ‖rootInput gamma hg chi modes u hu centers hc tau i‖ ^ 2 *
          ∫ x : T3, ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2 := by
  simpa only [firstDerivativeAction, derivativeInput, norm_complexifyVector] using
    (kernelAction_memLp_two_and_energy_le _ (integrable_periodicKernel N hN t e .undifferentiated)
      _ (rootInput gamma hg chi modes u hu centers hc tau i)
      (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).2.2

theorem secondDerivativeAction_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    (∫ x : T3, ‖secondDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j x‖ ^ 2) ≤
      (∫ q : T6, ‖periodicKernel N hN t e .undifferentiated q‖) ^ 2 *
        ‖rootInput gamma hg chi modes u hu centers hc tau i‖ ^ 2 *
          ∫ x : T3, ‖coordinateDerivative gamma chi modes u centers tau i j x‖ ^ 2 := by
  simpa only [secondDerivativeAction, derivativeInput, norm_complexifyVector] using
    (kernelAction_memLp_two_and_energy_le_right _ (integrable_periodicKernel N hN t e .undifferentiated)
      (rootInput gamma hg chi modes u hu centers hc tau i) _
      (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)).2.2

/-- Identification with the actual weak derivative, including the Fourier normalization. -/
theorem first_channel_eq_ae (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    (fun x ↦ (PancakePeriodicVorticityEquation.unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.first j))
        (rootInput gamma hg chi modes u hu centers hc tau i)
        (rootInput gamma hg chi modes u hu centers hc tau i) x) =ᵐ[volume]
      firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j :=
  PressureCoherentWeakFieldTransfer.first_channel_eq_ae N hN t e j
    (rootVorticity gamma chi modes u centers tau i)
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i)
    (rootInput gamma hg chi modes u hu centers hc tau i)

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction
