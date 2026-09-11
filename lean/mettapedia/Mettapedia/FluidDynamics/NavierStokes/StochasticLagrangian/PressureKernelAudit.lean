import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootKernelBudget

/-! Regressions for the physical kernel, excluded modes, and vorticity zeros. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureKernelAudit

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open FinitePressureKernel PressureKernelAction PressureKernelFourier PressureBilinearOperator
open GaussianRootKernelBudget LocalLowDiffusionBudget

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

example (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (u v : C3) (x : T3) :
    kernelAction (pressureKernel e he {k} {p})
      (fun y ↦ UnitAddTorus.mFourier k y • u)
      (fun y ↦ UnitAddTorus.mFourier p y • v) x =
    (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
      pressurePairOperator e he k p u v := by
  rw [kernelAction_monomials _ (continuous_pressureKernel e he {k} {p}),
    mFourierCoeff_pressureKernel, if_pos (by simp)]

/-- A mode outside the retained first-input support is annihilated. -/
example (e : R3) (he : ‖e‖ = 1) (S T : Finset Wavevector) (k p : Wavevector)
    (hk : k ∉ S) (u v : C3) (x : T3) :
    kernelAction (pressureKernel e he S T)
      (fun y ↦ UnitAddTorus.mFourier k y • u)
      (fun y ↦ UnitAddTorus.mFourier p y • v) x = 0 := by
  rw [kernelAction_monomials _ (continuous_pressureKernel e he S T),
    mFourierCoeff_pressureKernel, if_neg (fun h ↦ hk h.1)]
  simp

example (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3) (f g : T3 → C3)
    (hK : Continuous K) (hf : Continuous f) (hg : Continuous g) (x : T3) :
    (2 * 3 : ℂ) • kernelAction K f g x -
      kernelAction K (fun y ↦ (2 : ℂ) • f y) (fun y ↦ (3 : ℂ) • g y) x = 0 := by
  rw [kernelAction_localization K f g (fun _ ↦ 2) (fun _ ↦ 3) x
    hK hf hg continuous_const continuous_const]
  simp

example (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3) (g : T3 → C3) (x : T3) :
    kernelAction K (fun _ ↦ 0) g x = 0 := by simp [kernelAction]

/-- The first weighted difference vanishes at zero input vorticity. -/
example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y z : T3)
    (hy : fullVorticity u y = 0) :
    rootLocalizationDensity gamma chi modes u centers tau i x y z = 0 := by
  simp [rootLocalizationDensity, rootDifferenceCost, hy]

/-- The second weighted difference also vanishes at zero input vorticity. -/
example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y z : T3)
    (hz : fullVorticity u z = 0) :
    rootLocalizationDensity gamma chi modes u centers tau i x y z = 0 := by
  simp [rootLocalizationDensity, rootDifferenceCost, hz]

end Mettapedia.FluidDynamics.NavierStokes.PressureKernelAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearOperator.norm_pressurePairLinear_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearOperator.pressurePairOperator_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearOperator.norm_pressurePairOperator_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.first_pairWavevector
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.second_pairWavevector
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.mem_pairModes_iff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.continuous_pressureKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.integrable_pressureKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel.mFourierCoeff_pressureKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction.integrable_action_integrand
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction.kernelAction_localization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction.norm_kernelAction_localization_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction.kernelAction_monomials
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.continuous_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.kernelAction_vectorPolynomial
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.pressureKernelAction_vectorPolynomial_of_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.vectorPolynomial_pairConvolution_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.pressureKernelAction_eq_pairConvolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier.pressureHessian_polynomial_eq_neg_kernelAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootKernelBudget.norm_rootLocalization_integrand_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootKernelBudget.norm_pressureKernel_rootLocalization_le
