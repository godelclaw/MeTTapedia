import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalJointDiffusionBudget

/-!
# Two actual spatial derivatives of full vorticity

A summable third velocity moment supplies the two derivatives of curl.
The translation curve is twice continuously differentiable and its
derivatives are the full Fourier fields, without a receiver truncation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpatialVorticityJets

open scoped ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian PancakeIndexedFourierMoments
open PancakeInfiniteSpatialCurl PancakeHigherDerivativeMoments PancakeFourierTranslationCurve
open InfiniteFourierDiffusion LocalLowDiffusionBudget LocalJointDiffusionBudget
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def fullCurlGradient (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (fullFourierField id (indexedDerivativeCoeff id j (fourierCurl u)) x)

theorem contDiff_fullVorticity_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    ContDiff ℝ 2 (fun h : ℝ ↦ fullVorticity u (x + coordinateShift j h)) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw2 := summable_secondMoment_curl u hu
  have hw1 : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _ hw2
  have hw0 := summable_norm_coefficients id _ hw1
  have hwd := summable_norm_derivativeCoefficients id _ hw1 j
  have hwdd := summable_norm_secondDerivative _ hw2 j j
  have h := complexRealPartEuclideanCLM.contDiff.comp
    ((ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).contDiff.comp
      (contDiff_fullTranslationCurve _ hw0 j hwd hwdd))
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply,
    fullTranslationCurve_apply id _ hw0, fullVorticity, spatialCurl_velocity u hu1] using h

theorem hasDerivAt_fullVorticity_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t : ℝ ↦ fullVorticity u (x + coordinateShift j t))
      (fullCurlGradient u j (x + coordinateShift j h)) h := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw1 : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _ (summable_secondMoment_curl u hu)
  have hd := hasDerivAt_fullFourierField_shift id (fourierCurl u)
    (summable_norm_coefficients id _ hw1) j (summable_norm_derivativeCoefficients id _ hw1 j) h x
  simp only [fullVorticity, spatialCurl_velocity u hu1, fullCurlGradient]
  convert! complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h hd using 1

theorem hasDerivAt_fullCurlGradient_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t : ℝ ↦ fullCurlGradient u j (x + coordinateShift j t))
      (fullCurlSecond u j (x + coordinateShift j h)) h := by
  have hw2 := summable_secondMoment_curl u hu
  have hw1 : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second _ hw2
  have hd := hasDerivAt_fullFourierField_shift id (indexedDerivativeCoeff id j (fourierCurl u))
    (summable_norm_derivativeCoefficients id _ hw1 j) j (summable_norm_secondDerivative _ hw2 j j) h x
  exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h hd

theorem deriv_fullVorticity_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    deriv (fun t : ℝ ↦ fullVorticity u (x + coordinateShift j t)) =
      fun h ↦ fullCurlGradient u j (x + coordinateShift j h) :=
  funext (fun h ↦ (hasDerivAt_fullVorticity_shift u hu j x h).deriv)

theorem deriv_deriv_fullVorticity_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    deriv (deriv (fun t : ℝ ↦ fullVorticity u (x + coordinateShift j t))) 0 = fullCurlSecond u j x := by
  rw [deriv_fullVorticity_shift u hu]
  simpa only [coordinateShift_zero, add_zero] using (hasDerivAt_fullCurlGradient_shift u hu j x 0).deriv

end Mettapedia.FluidDynamics.NavierStokes.LocalSpatialVorticityJets
