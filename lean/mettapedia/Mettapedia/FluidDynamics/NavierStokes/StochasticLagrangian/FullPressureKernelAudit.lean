import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootPressureIdentification

/-! Regressions for the full-field coefficient action and its reality boundary. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullPressureKernelAudit

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureBilinearOperator PressureKernelAction FinitePressureKernel
open PressureKernelCoefficientAction FullVorticityFourierCoefficients
open FourierPressureTraceSymbol PancakeFrequencyProjectorCommutator
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Either empty retained input support annihilates the full-field action. -/
example (e : R3) (he : ‖e‖ = 1) (T : Finset Wavevector)
    (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g) (x : T3) :
    kernelAction (pressureKernel e he ∅ T) f g x = 0 ∧
      kernelAction (pressureKernel e he T ∅) f g x = 0 := by
  simp only [pressureKernelAction_eq_coefficient_sum e he _ _ f g hf hg, Finset.sum_empty,
    Finset.sum_const_zero, and_self]

/-- A singleton symbol still acts on the full continuous fields. -/
example (e : R3) (he : ‖e‖ = 1) (k p : Wavevector)
    (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g) (x : T3) :
    kernelAction (pressureKernel e he {k} {p}) f g x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        pressurePairOperator e he k p (UnitAddTorus.mFourierCoeff f k) (UnitAddTorus.mFourierCoeff g p) := by
  rw [pressureKernelAction_eq_coefficient_sum e he _ _ f g hf hg]
  simp only [Finset.sum_singleton]

/-- A missing retained coefficient kills the singleton action regardless of other modes. -/
example (e : R3) (he : ‖e‖ = 1) (k p : Wavevector)
    (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g)
    (hk : UnitAddTorus.mFourierCoeff f k = 0) (x : T3) :
    kernelAction (pressureKernel e he {k} {p}) f g x = 0 := by
  rw [pressureKernelAction_eq_coefficient_sum e he _ _ f g hf hg]
  simp [hk]

/-- Complexification of a real part is not the identity on arbitrary complex data. -/
example :
    complexifyVector (complexRealPartEuclideanCLM (fun _ : Fin 3 ↦ Complex.I)) = 0 ∧
      coefficientVec (fun _ : Fin 3 ↦ Complex.I) ≠ 0 := by
  constructor
  · ext i
    simp [complexifyVector, coefficientVec, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean]
  · intro h
    have hi := congrArg (fun v : C3 ↦ v 0) h
    simp [coefficientVec] at hi

end Mettapedia.FluidDynamics.NavierStokes.FullPressureKernelAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction.pressureKernel_eq_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction.kernelAction_character
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction.pressureKernelAction_eq_coefficient_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction.pressureKernelAction_eq_coefficient_convolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients.mFourierCoeff_coefficientVec
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients.summable_norm_fourierCurl
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients.complexify_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullVorticityFourierCoefficients.mFourierCoeff_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPressureIdentification.pressureKernelAction_fullVorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPressureIdentification.pressureHessian_polynomial_eq_neg_fullVorticity_kernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootPressureIdentification.norm_rootWeighted_pressure_add_localizedKernel_le
