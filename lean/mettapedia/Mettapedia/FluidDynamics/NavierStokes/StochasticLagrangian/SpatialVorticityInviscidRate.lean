import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialNavierStokesTangent
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionTransport

/-!
# Actual inviscid vorticity and curl-vorticity rates

The rates are reconstructed from the infinite momentum RHS. Axial
contraction removes the pressure Hessian and identifies common advection.
The curl-vorticity source remains the actual pressure/derivative source.
These are spatial identities, not assumed laws for independent fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialVorticityInviscidRate

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeGalerkinKineticEnergy
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian PancakeInfiniteFourierDerivative
open PancakeIndexedFourierMoments PancakeFourierMaterialPaths PancakeFourierTranslationCurve
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeLocalProjectedEquation
open PancakeMatrixDifferentialSymmetry PancakeMatrixCurlAlgebra PancakeSpatialGradientDifferentiation
open PancakeInfinitePressureHessian PancakeInfiniteSpatialPressure PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeLocalStrainReality PancakePhysicalNonlinearReconstruction
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation LocalProjectionTransport
open LocalHelicitySourceEvolution LocalHelicityCenterEvolution LocalVorticitySeparation
open PancakeSpatialGradientRegularity PancakeBlockReality PancakeInfiniteRealCurl LocalAlignmentForcing
open PancakeInfiniteDirectionalTransport VelocityRHSMoments

local notation "T3" => UnitAddTorus (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

theorem matrixCurl_matrixTransport (U : T3 → VelocityCoefficient) (A : T3 → M3) (x : T3)
    (hA : ∀ j, DifferentiableAt ℝ (fun t ↦ A (x + coordinateShift j t)) 0) :
    matrixCurl (matrixTransport U A x) = spatialTransport U (fun y ↦ matrixCurl (A y)) x := by
  rw [matrixTransport_eq_sum_derivative U A x hA]
  simp only [map_sum, map_smul, spatialTransport, coordinateDerivative_matrixCurl A _ x (hA _)]

theorem spatialCurl_inviscidRHS (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialCurl (fullFourierField id (infiniteVelocityRHS 0 u)) x +
      spatialTransport (fullFourierField id u) (spatialCurl (fullFourierField id u)) x =
        (spatialStrain (fullFourierField id u) x).mulVec (spatialCurl (fullFourierField id u) x) := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hA (j : Fin 3) : DifferentiableAt ℝ
      (fun t ↦ spatialVelocityGradient (fullFourierField id u) (x + coordinateShift j t)) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_velocityGradient_shift u hu2 j x)
  have hsq := matrixCurl_neg_square_trace_zero (spatialVelocityGradient (fullFourierField id u) x)
    (spatialDivergence_fullFourierField u hu2 hd x)
  rw [neg_mul, map_neg] at hsq
  have hp := matrixCurl_symmetric (spatialHessian (spatialPressure u) x)
    (spatialHessian_pressure_symmetric u hu2 x)
  have he := congrArg matrixCurl (SpatialNavierStokesTangent.gradient_infiniteVelocityRHS 0 u hu hd x)
  simp only [Complex.ofReal_zero, zero_smul, add_zero, map_sub, map_neg, hp, sub_zero,
    matrixCurl_velocityGradient, matrixCurl_matrixTransport _ _ x hA] at he
  change _ = (spatialStrain (fullFourierField id u) x).mulVec (spatialCurl (fullFourierField id u) x) at hsq
  rw [he, ← hsq]
  abel

theorem real_spatialTransport_curl (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 2 v))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    complexRealPartEuclideanCLM
      (spatialTransport (fullFourierField id u) (spatialCurl (fullFourierField id v)) x) =
        transportVorticity u v x := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  have hreal (j : Fin 3) : ((fullFourierField id u x j).re : ℂ) = fullFourierField id u x j := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (fullFourierField_im_zero u (summable_norm_coefficients id u hm) hr x j).symm
  have hw : Summable (indexedFirstMoment id (fourierCurl v)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 v hv
  simp only [spatialTransport, spatialCurl_velocity v (summable_firstMoment_of_second v hv),
    coordinateDerivative_fullFourierField id _ hw, map_sum, transportVorticity, fullCurlGradient]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hreal j]
  ext i
  simp [InfiniteFourierTransport.velocityComponent, complexRealPartEuclideanCLM_apply,
    complexRealPartEuclidean]

theorem fullVorticity_inviscidRHS (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    fullVorticity (infiniteVelocityRHS 0 u) x + transportVorticity u u x =
      fullStrainOperator u x (fullVorticity u x) := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hreal (i j : Fin 3) : (spatialStrain (fullFourierField id u) x i j).im = 0 := by
    have h := congrArg Complex.im (spatialStrain_reality u hu1 hr x i j)
    simp only [Complex.conj_im] at h
    linarith
  have he := congrArg complexRealPartEuclideanCLM (spatialCurl_inviscidRHS u hu hd x)
  rw [map_add, real_spatialTransport_curl u u hu1 hu2 hr x, complexRealPart_mulVec _ _ hreal] at he
  exact he

theorem fullVorticity_curl_inviscidRHS (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    fullVorticity (fourierCurl (infiniteVelocityRHS 0 u)) x + transportVorticity u (fourierCurl u) x =
      -gradient u x (fullVorticity (fourierCurl u) x) + source u x := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw1 := summable_fourierMoment_curl 1 u hu2
  have hw2 := summable_fourierMoment_curl 2 u hu3
  have hww1 := summable_fourierMoment_curl 1 (fourierCurl u) hw2
  have hRHS1 := summable_fourierMoment_curl 1 (infiniteVelocityRHS 0 u)
    (summable_fourierMoment_infiniteVelocityRHS 2 0 u hu)
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu1
  have hreal (j : Fin 3) : ((fullFourierField id u x j).re : ℂ) = fullFourierField id u x j := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (fullFourierField_im_zero u (summable_norm_coefficients id u hm) hr x j).symm
  have htr : complexRealPartEuclideanCLM
      (fullFourierField id (directionalCoeff (fourierCurl (fourierCurl u))
        (fun j ↦ (fullFourierField id u x j).re)) x) = transportVorticity u (fourierCurl u) x := by
    rw [fullFourierField_directionalCoeff_transport _ hww1 (fullFourierField id u) x hreal,
      ← spatialCurl_velocity (fourierCurl u) hw1]
    exact real_spatialTransport_curl u (fourierCurl u) hu1 hw2 hr x
  have he := curlVorticityMaterialRate_inviscid u hu hd hr x
  simp only [curlVorticityMaterialRate, map_add, htr] at he
  simpa only [fullVorticity, spatialCurl_velocity _ hRHS1] using he

end Mettapedia.FluidDynamics.NavierStokes.SpatialVorticityInviscidRate
