import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakChannelBudget

/-! Second-slot field identification and shifted patch-family checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureWeakChannelFamilyAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open PressureKernelAction PressureKernelSwap PressureCoherentChannelPeriodization
open PeriodicVectorWeakDerivative FourierPressureTraceSymbol PancakeBilinearPeriodization
open GaussianRootWeakPressureAction GaussianRootWeakChannelBudget
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (q : T6) :
    firstTorusDisplacement (swapTorus q) = secondTorusDisplacement q ∧
      secondTorusDisplacement (swapTorus q) = firstTorusDisplacement q :=
  ⟨firstDisplacement_swap q, secondDisplacement_swap q⟩

/-- No symmetry or continuity premise is required for this change of variables. -/
example (K : T6 → Op) (f g : T3 → C3) (x : T3) :
    kernelAction (swapKernel K) f g x = kernelAction K g f x :=
  kernelAction_swapKernel K f g x

/-- A constant second input contributes no second-coordinate derivative channel. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e v : R3) (j : Fin 3) (f : C(T3, C3)) :
    (fun x ↦ (unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.second j)) f (fun _ ↦ complexifyVector v) x) =ᵐ[volume]
      fun _ ↦ 0 := by
  have hd : coordinateRate (fun _ : T3 ↦ v) j = fun _ ↦ 0 := by
    funext x
    ext i
    simp [coordinateRate_apply, PancakeHaarTransportRate.shiftRate]
  have hz : complexifyVector (0 : R3) = 0 := by
    apply norm_eq_zero.mp
    simp only [norm_complexifyVector, norm_zero]
  have h := PressureCoherentWeakFieldTransfer.second_channel_eq_ae N hN t e j
    f (fun _ ↦ v) continuous_const (LipschitzWith.const v).locallyLipschitz
  filter_upwards [h] with x hx
  simpa only [hd, hz, kernelAction, map_zero, integral_zero] using hx

variable (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
variable (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers)

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    (fun x ↦ (unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.second j))
        (rootInput gamma hg chi modes u hu centers hc tau i)
        (rootInput gamma hg chi modes u hu centers hc tau i) x) =ᵐ[volume]
      secondDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j :=
  GaussianRootWeakPressureAction.second_channel_eq_ae gamma hg chi modes u hu centers hc tau i N hN t e j

include hg hu hc in
example (j : Fin 3) (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q) :
    Integrable (fun x : T3 ↦ ∫ q : T6, M q *
      twoPointDerivativeDensity gamma chi modes u centers tau j
        (x - secondTorusDisplacement q) (x - firstTorusDisplacement q)) :=
  (integrable_twoPointDerivativeDensity gamma hg chi modes u hu centers hc tau j M hM hMn
    secondTorusDisplacement firstTorusDisplacement (by fun_prop) (by fun_prop)).integral_prod_right

end Mettapedia.FluidDynamics.NavierStokes.PressureWeakChannelFamilyAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.measurePreserving_swapTorus
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.firstDisplacement_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.secondDisplacement_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.integrable_swapKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.integral_norm_swapKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.kernelAction_swapKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap.mFourierCoeff_swapKernel_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization.exists_uniform_periodic_mass_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction.smul_kernelAction_eq_ae_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.second_channel_eq_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.second_channel_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.exists_uniform_second_channel_derivative_energy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.second_channel_eq_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.sum_input_product_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.integrable_twoPointDerivativeDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.firstDerivativeAction_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.secondDerivativeAction_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.first_channel_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.second_channel_sum_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget.exists_uniform_channel_sum_envelope
