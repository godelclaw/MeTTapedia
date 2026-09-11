import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakPressureAction

/-! L² pressure action, zero-ratio energy, and actual weak-input checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureL2ActionAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open FourierPressureTraceSymbol PressureKernelAction PressureL2KernelAction
open PressureCoherentChannelPeriodization GaussianRootWeakPressureAction
open PressureCoherentDivergenceChannel (Factor)

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

example (f : T3 → R3) (hf : MemLp f 2) : MemLp (fun x ↦ complexifyVector (f x)) 2 :=
  PeriodicVectorWeakDerivative.memLp_complexify f hf

example (f g : T3 → C3) (x : T3) : kernelAction (fun _ : T6 ↦ 0) f g x = 0 := by
  simp [kernelAction]

example (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1) (c : Factor)
    (f : T3 → C3) (g : C(T3, C3)) (hf : MemLp f 2) :
    (∫ x : T3, ‖kernelAction (periodicKernel N hN 0 e c) f g x‖ ^ 2) = 0 := by
  obtain ⟨C, _, hC⟩ := exists_uniform_coherent_energy_bound
  have h := hC N hN 0 (by constructor <;> norm_num) e he c f g hf
  simp only [PressureLowOutputCutoff.ratio, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_mul] at h
  exact le_antisymm h (integral_nonneg (fun _ ↦ sq_nonneg _))

variable (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
variable (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers)

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    MemLp (firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j) 2 :=
  memLp_firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    MemLp (secondDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j) 2 :=
  memLp_secondDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    Integrable (fun x : T3 ↦ ‖firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j x‖ ^ 2) :=
  (memLp_firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j).norm.integrable_sq

end Mettapedia.FluidDynamics.NavierStokes.PressureL2ActionAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.memLp_complexify
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.kernelAction_memLp_two_and_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.kernelAction_memLp_two_and_energy_le_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.kernelAction_congr_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.exists_uniform_coherent_energy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.memLp_derivativeInput
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.ae_integrable_firstDerivativeAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.ae_integrable_secondDerivativeAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.memLp_firstDerivativeAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.memLp_secondDerivativeAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.firstDerivativeAction_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.secondDerivativeAction_energy_le
