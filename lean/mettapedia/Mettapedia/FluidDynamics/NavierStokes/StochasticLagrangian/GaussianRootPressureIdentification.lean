import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelCoefficientAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootKernelBudget

/-!
# Root localization of the actual retained pressure

The full vorticity fields enter the finite pressure kernel. Their recovered
coefficients identify the unlocalized term with the pressure Hessian of the
retained original velocity modes. The localized term retains the actual
root-weighted fields, without imposing divergence or zero-mean conditions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootPressureIdentification

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakeFourierPressureStrain
open FourierPressureTraceSymbol LocalLowDiffusionBudget FinitePressureKernel PressureKernelAction
open PressureKernelCoefficientAction FullVorticityFourierCoefficients
open GaussianRootVorticity GaussianRootKernelBudget PressureTwoInputReconstruction
open ComplexPressureConvolution PancakeFiniteFourierLocalization

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

theorem pressureKernelAction_fullVorticity (e : R3) (he : ‖e‖ = 1)
    (S T : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) :
    kernelAction (pressureKernel e he S T)
      (fun y ↦ complexifyVector (fullVorticity u y))
      (fun y ↦ complexifyVector (fullVorticity u y)) x =
      vectorPolynomial (finiteCutoffOutputModes S T)
        (pairConvolution e S T (fourierCurl u) (fourierCurl u)) x := by
  have hw := continuous_fullVorticity u hu
  have hc : Continuous (fun y ↦ complexifyVector (fullVorticity u y)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  rw [pressureKernelAction_eq_coefficient_convolution e he S T _ _ hc hc]
  simp only [mFourierCoeff_fullVorticity u hu hr, coefficientVec, WithLp.ofLp_toLp]

theorem pressureHessian_polynomial_eq_neg_fullVorticity_kernel
    (e : R3) (he : ‖e‖ = 1) (M : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (x : T3) :
    vectorPolynomial (finiteCutoffOutputModes M M)
        (fun q ↦ (pressureHessianCoeff M u q).trace • complexTiltSymbol e q) x =
      -kernelAction (pressureKernel e he M M)
        (fun y ↦ complexifyVector (fullVorticity u y))
        (fun y ↦ complexifyVector (fullVorticity u y)) x := by
  rw [pressureKernelAction_fullVorticity e he M M u hu hr]
  simp only [vectorPolynomial, PhysicalPressurePair.pressureHessian_tilt_eq_pairConvolution e M u hd,
    smul_neg, Finset.sum_neg_distrib]

theorem norm_rootWeighted_pressure_add_localizedKernel_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers)
    (e : R3) (he : ‖e‖ = 1) (M : Finset Wavevector)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) (x : T3) :
    let c := rootPatch gamma chi modes u centers tau i
    let w := fun y ↦ complexifyVector (fullVorticity u y)
    let B := pressureKernel e he M M
    ‖((c x : ℂ) * (c x : ℂ)) • vectorPolynomial (finiteCutoffOutputModes M M)
        (fun q ↦ (pressureHessianCoeff M u q).trace • complexTiltSymbol e q) x +
      kernelAction B (fun y ↦ (c y : ℂ) • w y) (fun y ↦ (c y : ℂ) • w y) x‖ ≤
      ∫ q : T6, ‖B q‖ * rootLocalizationDensity gamma chi modes u centers tau i
        x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) := by
  dsimp only
  rw [pressureHessian_polynomial_eq_neg_fullVorticity_kernel e he M u hu hr hd,
    smul_neg, neg_add_eq_sub, norm_sub_rev]
  exact norm_pressureKernel_rootLocalization_le gamma hg chi modes u hu centers hc tau i e he M M x

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootPressureIdentification
