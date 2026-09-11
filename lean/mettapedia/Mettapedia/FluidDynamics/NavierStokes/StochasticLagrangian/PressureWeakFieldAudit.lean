import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakPressureAction

/-! Fourier reconstruction, weak-field normalization, and derivative-cost checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureWeakFieldAudit

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail
open PressureKernelAction PressureL2KernelAction PressureCoherentChannelPeriodization
open PeriodicVectorWeakDerivative FourierPressureTraceSymbol
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)
open Mettapedia.Analysis
open scoped Topology

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Projection convergence accepts an L² function without a continuity premise. -/
example (f : T3 → C3) (hf : MemLp f 2) :
    Tendsto (fun P : Finset Wavevector ↦
      ∫ x : T3, ‖UnitTorusL2Projection.vectorProjection f P x - f x‖ ^ 2) atTop (𝓝 0) :=
  UnitTorusL2Projection.tendsto_integral_vectorProjection_error f hf

/-- The uniform approximation theorem does not assume a nonempty component type. -/
example (f : C(T3, EuclideanSpace ℂ Empty)) :
    ∃ P : Finset Wavevector, ∃ v : Wavevector → EuclideanSpace ℂ Empty,
      ‖f - UnitTorusFourierApproximation.polynomial P v‖ < 1 :=
  UnitTorusFourierApproximation.exists_polynomial_approximation f (by norm_num)

example (v : R3) (j : Fin 3) (x : T3) : coordinateRate (fun _ : T3 ↦ v) j x = 0 := by
  ext i
  simp [coordinateRate_apply, PancakeHaarTransportRate.shiftRate]

/-- A constant first input contributes no first-coordinate derivative channel. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e v : R3) (j : Fin 3) (g : C(T3, C3)) :
    (fun x ↦ (unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.first j)) (fun _ ↦ complexifyVector v) g x) =ᵐ[volume]
      fun _ ↦ 0 := by
  have hd : coordinateRate (fun _ : T3 ↦ v) j = fun _ ↦ 0 := by
    funext x
    ext i
    simp [coordinateRate_apply, PancakeHaarTransportRate.shiftRate]
  have hz : complexifyVector (0 : R3) = 0 := by
    apply norm_eq_zero.mp
    simp only [norm_complexifyVector, norm_zero]
  have h := PressureCoherentWeakFieldTransfer.first_channel_eq_ae N hN t e j
    (fun _ ↦ v) continuous_const (LipschitzWith.const v).locallyLipschitz g
  filter_upwards [h] with x hx
  simpa only [hd, hz, kernelAction, map_zero, zero_apply, integral_zero] using hx

example (N : ℝ) (hN : 0 < N) : ‖unitTorusDerivativePhase * (N : ℂ)‖ = 2 * Real.pi * N := by
  rw [norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]

variable (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
variable (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers)

open GaussianRootWeakPressureAction in
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3) :
    (fun x ↦ (unitTorusDerivativePhase * (N : ℂ)) •
      kernelAction (periodicKernel N hN t e (.first j))
        (rootInput gamma hg chi modes u hu centers hc tau i)
        (rootInput gamma hg chi modes u hu centers hc tau i) x) =ᵐ[volume]
      firstDerivativeAction gamma hg chi modes u hu centers hc tau i N hN t e j :=
  first_channel_eq_ae gamma hg chi modes u hu centers hc tau i N hN t e j

end Mettapedia.FluidDynamics.NavierStokes.PressureWeakFieldAudit

#print axioms Mettapedia.Analysis.L2IntegralEnergy.norm_sub_toLp_sq
#print axioms Mettapedia.Analysis.L2IntegralEnergy.tendsto_toLp_of_integral_sub_sq
#print axioms Mettapedia.Analysis.UnitTorusL2Projection.tendsto_integral_projection_error
#print axioms Mettapedia.Analysis.UnitTorusL2Projection.mFourierCoeff_vector_apply
#print axioms Mettapedia.Analysis.UnitTorusL2Projection.vectorProjection_eq_sum
#print axioms Mettapedia.Analysis.UnitTorusL2Projection.tendsto_integral_vectorProjection_error
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.exists_polynomial_approximation
#print axioms Mettapedia.Analysis.UnitTorusFourierApproximation.dense_polynomial_range
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.kernelAction_sub_left_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.kernelAction_sub_right_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.smul_toLpAction_eq_iff
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.tendsto_toLpAction_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction.tendsto_toLpAction_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction.kernelAction_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction.smul_toLpAction_polynomial_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction.smul_kernelAction_eq_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.first_channel_eq_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.first_channel_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentWeakFieldTransfer.exists_uniform_first_channel_derivative_energy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakPressureAction.first_channel_eq_ae
