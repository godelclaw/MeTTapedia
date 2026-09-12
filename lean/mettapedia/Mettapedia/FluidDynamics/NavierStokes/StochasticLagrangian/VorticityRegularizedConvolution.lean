import Mettapedia.Analysis.PeriodicRieszOperatorFourier
import Mettapedia.Analysis.UnitTorusIntegrableConvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityWeightedStretching

/-!
# Regularized Riesz entries acting on the actual vorticity

The scalar entry convolutions are identified with the actual curl Fourier
coefficients. Uniform convergence of the field series, not a uniform
unweighted bound on the regularizing kernels, justifies the integration.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedConvolution

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakeGalerkinKineticEnergy PancakeInfiniteFourierDerivative
open PancakeFourierTranslationCurve FullVorticityFourierCoefficients LocalLowDiffusionBudget
open Mettapedia.Analysis UnitTorusIntegrableConvolution
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def curlComponent (u : FourierVelocity) (j : Fin 3) : C(T3, ℂ) :=
  (ContinuousLinearMap.proj j : VelocityCoefficient →L[ℂ] ℂ).compLeftContinuous ℂ T3
    (fullFourierField id (fourierCurl u))

theorem hasSum_curlComponent (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (j : Fin 3) :
    HasSum (fun k ↦ fourierCurl u k j • UnitAddTorus.mFourier k) (curlComponent u j) := by
  have hs := ((ContinuousLinearMap.proj j : VelocityCoefficient →L[ℂ] ℂ).compLeftContinuous ℂ T3).hasSum
    (summable_modeField id (fourierCurl u) (summable_norm_fourierCurl u hu)).hasSum
  apply hs.congr_fun
  intro k
  ext x
  change fourierCurl u k j * UnitAddTorus.mFourier k x =
    UnitAddTorus.mFourier k x * fourierCurl u k j
  ring

theorem curlComponent_apply (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (j : Fin 3) (x : T3) :
    curlComponent u j x = (fullVorticity u x j : ℂ) := by
  have h := congrArg (fun z ↦ z j) (complexify_fullVorticity u hu hr x)
  exact h.symm

theorem hasSum_entry_convolution (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (i j l : Fin 3) (N : ℕ) (x : T3) :
    HasSum (fun k : Wavevector ↦
      ((AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) *
        AnnularRieszKernel.rieszEntry i j (UnitTorusLattice.frequency k) : ℝ) : ℂ) *
        UnitAddTorus.mFourier k x * fourierCurl u k l)
      ((∫ h : T3, PeriodicRieszOperator.entryKernel i j N h * fullVorticity u (x - h) l : ℝ) : ℂ) := by
  have h := hasSum_convolution (fun h ↦ (PeriodicRieszOperator.entryKernel i j N h : ℂ))
    (PeriodicRieszOperator.integrable_entryKernel i j N).ofReal
    (curlComponent u l) (fun k ↦ fourierCurl u k l) (hasSum_curlComponent u hu l) x
  simp only [PeriodicRieszOperator.mFourierCoeff_entryKernel, curlComponent_apply u hu hr,
    ← Complex.ofReal_mul, _root_.integral_complex_ofReal] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedConvolution
