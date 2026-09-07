import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMatrixDifferentialSymmetry

/-!
# Ordinary first and second spatial derivatives of the velocity gradient

The same third absolute velocity moment supplies the matrix regularity
needed to commute symmetrization with transport and diffusion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialGradientRegularity

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeInfiniteSpatialCurl PancakeInfiniteFourierDerivative
open PancakeLocalGradientEquation PancakeMatrixDifferentialSymmetry
open PancakeSpatialGradientDifferentiation PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)

theorem hasDerivAt_coordinateDerivative2_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (l m n : Fin 3) (x : T3) :
    HasDerivAt
      (fun h ↦ coordinateDerivative
        (fun y ↦ coordinateDerivative (fullFourierField id u) l y) m (x + coordinateShift n h))
      (coordinateDerivative
        (fun y ↦ coordinateDerivative (fun z ↦ coordinateDerivative (fullFourierField id u) l z) m y)
        n x) 0 := by
  rw [coordinateDerivative_fullFourierField_eq u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) l]
  exact hasDerivAt_coordinateDerivative_shift_zero (indexedDerivativeCoeff id l u)
    (summable_fourierMoment_derivative 2 u hu l) m n x

theorem hasDerivAt_velocityGradient_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (m : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ spatialVelocityGradient (fullFourierField id u) (x + coordinateShift m h))
      (fun i j ↦ coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) m x i)
      0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_coordinateDerivative_shift_zero u hu j m x)) i

theorem matrixCoordinateDerivative_velocityGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (m : Fin 3) (x : T3) :
    matrixCoordinateDerivative (spatialVelocityGradient (fullFourierField id u)) m x =
      fun i j ↦ coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) m x i :=
  HasDerivAt.deriv (F := Fin 3 → Fin 3 → ℂ) (hasDerivAt_velocityGradient_shift u hu m x)

theorem hasDerivAt_matrixDerivative_gradient_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (m n : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ matrixCoordinateDerivative
      (spatialVelocityGradient (fullFourierField id u)) m (x + coordinateShift n h))
      (fun i j ↦ coordinateDerivative
        (fun y ↦ coordinateDerivative (fun z ↦ coordinateDerivative (fullFourierField id u) j z) m y)
        n x i) 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  simp only [matrixCoordinateDerivative_velocityGradient u hu2]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_coordinateDerivative2_shift u hu j m n x)) i

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpatialGradientRegularity
