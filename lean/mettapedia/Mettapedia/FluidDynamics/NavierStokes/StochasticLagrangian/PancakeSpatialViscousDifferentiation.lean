import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialGradientDifferentiation

/-!
# Differentiated viscosity from ordinary third derivatives

The coordinate derivative of the velocity Laplacian is the Laplacian of
its coordinate derivative, with all series paid by the third moment.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialViscousDifferentiation

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeHigherDerivativeMoments PancakeCurlOutputTail PancakeInfiniteSpatialLaplacian
open PancakeInfiniteSpatialCurl PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy
open PancakeFourierTranslationCurve PancakeHaarTransportRate PancakeSpatialGradientDifferentiation

local notation "T3" => UnitAddTorus (Fin 3)

theorem firstMoment_laplacianCoeff_le (u : FourierVelocity) (q : Wavevector) :
    fourierMoment 1 (laplacianCoeff u) q ≤ (2 * Real.pi)^2 * fourierMoment 3 u q := by
  change (1 + ‖frequencyVec q‖)^1 *
    ‖(unitTorusDerivativePhase^2 * modeSquare q) • coefficientVec (u q)‖ ≤ _
  rw [pow_one, norm_smul, norm_mul, norm_pow, norm_derivativePhase, norm_modeSquare]
  calc
    _ ≤ (1 + ‖frequencyVec q‖) *
        ((2 * Real.pi)^2 * (1 + ‖frequencyVec q‖)^2 * ‖coefficientVec (u q)‖) := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by unfold fourierMoment; ring

theorem summable_firstMoment_laplacianCoeff (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Summable (fourierMoment 1 (laplacianCoeff u)) :=
  (hu.mul_left ((2 * Real.pi)^2)).of_nonneg_of_le (fourierMoment_nonneg _ _)
    (firstMoment_laplacianCoeff_le u)

theorem indexedDerivativeCoeff_laplacian (u : FourierVelocity) (j : Fin 3) :
    indexedDerivativeCoeff id j (laplacianCoeff u) = laplacianCoeff (indexedDerivativeCoeff id j u) := by
  funext q i
  simp only [indexedDerivativeCoeff, laplacianCoeff, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_spatialLaplacian_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ spatialLaplacian (fullFourierField id u) (x + coordinateShift j h))
      (spatialLaplacian (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x) 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hl : Summable (indexedFirstMoment id (laplacianCoeff u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_laplacianCoeff u hu
  have hd := hasDerivAt_fullFourierField_shift id (laplacianCoeff u)
    (summable_norm_coefficients id _ hl) j (summable_norm_derivativeCoefficients id _ hl j) 0 x
  rw [coordinateDerivative_fullFourierField_eq u hu1 j,
    spatialLaplacian_fullFourierField u hu2,
    spatialLaplacian_fullFourierField _ (summable_fourierMoment_derivative 2 u hu j)]
  simpa only [coordinateShift_zero, add_zero, indexedDerivativeCoeff_laplacian] using hd

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialViscousDifferentiation
