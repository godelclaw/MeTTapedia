import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullLambVector
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityGradientEvolution

/-!
# Differentiated vorticity transport for the full Fourier field

The material gradient rate is derived from the inviscid vorticity equation.
The velocity-gradient commutator is retained separately from the actual
derivative of stretching. No independent Hessian or transport law is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullVorticityGradientTransport

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeInfiniteSpatialLaplacian PancakeInfiniteRealCurl PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths PancakeCoefficientLimitEquation
open PancakeInfiniteDirectionalTransport VelocityRHSMoments FullLambVector
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityGradientEvolution
open LocalVorticityDiffusion
open LocalWeightedCurlCancellation
open LocalVorticitySeparation LocalProjectionTransport SpatialVorticityInviscidRate LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem fullVorticity_eq_realFullField (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : fullVorticity u = realFullField (fourierCurl u) := by
  funext x
  simp only [fullVorticity, realFullField, spatialCurl_velocity u hu]

theorem hasDerivAt_fullVorticity_shift_second (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ fullVorticity u (x + coordinateShift j t))
      (fullCurlGradient u j (x + coordinateShift j h)) h := by
  rw [fullVorticity_eq_realFullField u (summable_firstMoment_of_second u hu)]
  exact hasDerivAt_realFullField_shift (fourierCurl u) (summable_fourierMoment_curl 1 u hu) j x h

def mixedGradient (u : FourierVelocity) (j k : Fin 3) (x : T3) : R3 :=
  velocityJet (indexedDerivativeCoeff id j u) k x

theorem mixedGradient_commute (u : FourierVelocity) (j k : Fin 3) (x : T3) :
    mixedGradient u j k x = mixedGradient u k j x := by
  simp only [mixedGradient, velocityJet, indexedDerivativeCoeff_commute u k j]

theorem hasDerivAt_velocityJet_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ velocityJet u j (x + coordinateShift k t))
      (mixedGradient u j k (x + coordinateShift k h)) h :=
  hasDerivAt_realFullField_shift _ (summable_firstMoment_derivative u hu j) k x h

theorem hasDerivAt_fullCurlGradient_shift_mixed (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ fullCurlGradient u j (x + coordinateShift k t))
      (mixedGradient (fourierCurl u) j k (x + coordinateShift k h)) h :=
  hasDerivAt_velocityJet_shift _ (summable_fourierMoment_curl 2 u hu) j k x h

theorem real_directionalCoeff (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (v : X3) (x : T3) :
    complexRealPartEuclideanCLM (fullFourierField id (directionalCoeff u v) x) =
      ∑ j, v j • velocityJet u j x := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  rw [fullFourierField_directionalCoeff u hu]
  simp only [map_sum, coordinateDerivative_fullFourierField id u hm]
  apply Finset.sum_congr rfl
  intro j _
  ext i
  simp [velocityJet, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

def stretchingDerivative (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  (∑ k, fullCurlGradient u j x k • velocityJet u k x) +
    ∑ k, fullVorticity u x k • mixedGradient u k j x

def transportCommutator (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  ∑ k, velocityJet u j x k • fullCurlGradient u k x

theorem hasDerivAt_stretching_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun t ↦ ∑ k : Fin 3,
      fullVorticity u (x + coordinateShift j t) k • velocityJet u k (x + coordinateShift j t))
      (stretchingDerivative u j x) 0 := by
  have ha := hasDerivAt_fullVorticity_shift_second u hu j x 0
  have hak (k : Fin 3) : HasDerivAt (fun t ↦ fullVorticity u (x + coordinateShift j t) k)
      (fullCurlGradient u j (x + coordinateShift j 0) k) 0 := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const 0 (EuclideanSpace.single k (1 : ℝ))).inner ℝ ha
  have h (k : Fin 3) := (hak k).smul (hasDerivAt_velocityJet_shift u hu k j x 0)
  simpa only [Function.comp_def, Pi.smul_apply', coordinateShift_zero, add_zero,
    Finset.sum_add_distrib, stretchingDerivative, add_comm]
    using HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ h k)

theorem hasDerivAt_transportVorticity_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun t ↦ transportVorticity u u (x + coordinateShift j t))
      (transportCommutator u j x +
        ∑ k, realFullField u x k • mixedGradient (fourierCurl u) j k x) 0 := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have ha := hasDerivAt_realFullField_shift u hu1 j x 0
  have hak (k : Fin 3) : HasDerivAt (fun t ↦ realFullField u (x + coordinateShift j t) k)
      (velocityJet u j (x + coordinateShift j 0) k) 0 := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const 0 (EuclideanSpace.single k (1 : ℝ))).inner ℝ ha
  have h (k : Fin 3) := (hak k).smul (hasDerivAt_fullCurlGradient_shift_mixed u hu k j x 0)
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ h k)
  simpa only [Function.comp_def, Pi.smul_apply', coordinateShift_zero, add_zero,
    Finset.sum_add_distrib, add_comm,
    transportCommutator, mixedGradient_commute (fourierCurl u) _ j,
    transportVorticity, InfiniteFourierTransport.velocityComponent, realFullField,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply] using hh

theorem fullCurlGradient_inviscidRHS (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (x : T3) :
    fullCurlGradient (infiniteVelocityRHS 0 u) j x =
      stretchingDerivative u j x - (transportCommutator u j x +
        ∑ k, realFullField u x k • mixedGradient (fourierCurl u) j k x) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  have he (y : T3) : fullVorticity (infiniteVelocityRHS 0 u) y =
      (∑ k, fullVorticity u y k • velocityJet u k y) - transportVorticity u u y := by
    rw [directional_velocityJet u hu1, gradient_vorticity]
    exact eq_sub_iff_add_eq.mpr (fullVorticity_inviscidRHS u hu3 hd hr y)
  have hR := hasDerivAt_fullVorticity_shift_second (infiniteVelocityRHS 0 u)
    (summable_fourierMoment_infiniteVelocityRHS 2 0 u hu) j x 0
  have h := (hasDerivAt_stretching_shift u hu2 j x).sub (hasDerivAt_transportVorticity_shift u hu3 j x)
  change HasDerivAt (fun t ↦ (∑ k : Fin 3,
    fullVorticity u (x + coordinateShift j t) k • velocityJet u k (x + coordinateShift j t)) -
      transportVorticity u u (x + coordinateShift j t)) _ 0 at h
  simp_rw [← he] at h
  simpa only [coordinateShift_zero, add_zero] using hR.unique h

theorem gradientMaterialRate_inviscid (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (x : T3) :
    gradientMaterialRate 0 u (fun k ↦ realFullField u x k) j x =
      stretchingDerivative u j x - transportCommutator u j x := by
  have hw2 := summable_fourierMoment_curl 2 u
    (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu)
  unfold gradientMaterialRate
  rw [map_add, real_directionalCoeff _ (summable_firstMoment_derivative _ hw2 j)]
  change fullCurlGradient (infiniteVelocityRHS 0 u) j x +
    (∑ k, realFullField u x k • mixedGradient (fourierCurl u) j k x) = _
  rw [fullCurlGradient_inviscidRHS u hu hd hr]
  abel

theorem gradientMaterialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (x : T3) :
    gradientMaterialRate ν u (fun k ↦ realFullField u x k) j x =
      stretchingDerivative u j x - transportCommutator u j x + ν • gradientLaplacian u j x := by
  rw [gradientMaterialRate_eq_inviscid_add_diffusion ν u hu,
    gradientMaterialRate_inviscid u hu hd hr]

end Mettapedia.FluidDynamics.NavierStokes.FullVorticityGradientTransport
