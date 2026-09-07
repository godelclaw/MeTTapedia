import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityGradientTime

/-!
# Ordinary derivatives of advection and the pressure gradient

The product rule separates the derivative of advection into transported
velocity gradient and its quadratic self-interaction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialGradientDifferentiation

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeHigherDerivativeMoments PancakeInfiniteSpatialLaplacian PancakePhysicalConvectionCoefficients
open PancakeInfiniteSpatialPressure PancakeInfinitePressureCoefficients PancakeInfinitePressureHessian
open PancakeFourierTranslationCurve PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)

def spatialTransport (u v : T3 → VelocityCoefficient) (x : T3) : VelocityCoefficient :=
  ∑ m : Fin 3, u x m • coordinateDerivative v m x

def gradientProduct (u : T3 → VelocityCoefficient) (j : Fin 3) (x : T3) : VelocityCoefficient :=
  ∑ m : Fin 3, coordinateDerivative u j x m • coordinateDerivative u m x

theorem hasDerivAt_fullFourierField_shift_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ fullFourierField id u (x + coordinateShift j h))
      (coordinateDerivative (fullFourierField id u) j x) 0 := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  rw [coordinateDerivative_fullFourierField id u hm j x]
  simpa only [coordinateShift_zero, add_zero] using
    hasDerivAt_fullFourierField_shift id u (summable_norm_coefficients id u hm) j
      (summable_norm_derivativeCoefficients id u hm j) 0 x

theorem hasDerivAt_coordinateDerivative_shift_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (m j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ coordinateDerivative (fullFourierField id u) m (x + coordinateShift j h))
      (coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) m y) j x) 0 := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  simpa only [coordinateDerivative_fullFourierField id u hm] using
    hasDerivAt_fullFourierField_shift_zero (indexedDerivativeCoeff id m u)
      (summable_firstMoment_derivative u hu m) j x

theorem hasDerivAt_spatialAdvection_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ spatialAdvection (fullFourierField id u) (x + coordinateShift j h))
      (spatialTransport (fullFourierField id u)
          (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x +
        gradientProduct (fullFourierField id u) j x) 0 := by
  have hU := hasDerivAt_fullFourierField_shift_zero u (summable_firstMoment_of_second u hu) j x
  have h (m : Fin 3) :=
    ((hasDerivAt_pi.mp hU) m).smul (hasDerivAt_coordinateDerivative_shift_zero u hu m j x)
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun m _ ↦ h m)
  simpa only [coordinateShift_zero, add_zero, coordinateDerivative2_commute u hu j,
    Finset.sum_add_distrib, spatialAdvection, spatialTransport, gradientProduct, Pi.smul_apply'] using hh

theorem hasDerivAt_spatialGradient_pressure_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ spatialGradient (spatialPressure u) (x + coordinateShift j h))
      (fun i ↦ spatialHessian (spatialPressure u) x i j) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have hh := hasDerivAt_fullFourierField_shift id
    (indexedDerivativeCoeff id i (infinitePressureCoeff u))
    (summable_norm_infinitePressureDerivative u hu i) j
    (summable_norm_infinitePressureSecondDerivative u hu i j) 0 x
  simpa only [spatialGradient, spatialHessian, spatialPressure,
    scalarCoordinateDerivative_fullFourierField _ (summable_norm_infinitePressure u hu) i
      (summable_norm_infinitePressureDerivative u hu i),
    scalarCoordinateDerivative_fullFourierField _ (summable_norm_infinitePressureDerivative u hu i) j
      (summable_norm_infinitePressureSecondDerivative u hu i j),
    coordinateShift_zero, add_zero] using hh

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialGradientDifferentiation
