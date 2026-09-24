import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalGradientEquation

/-!
# The ordinary spatial gradient of the Navier–Stokes vector field

This is an identity for the actual infinite Fourier right-hand side,
before a solution curve is introduced. It is useful for testing necessary
instantaneous estimates on smooth data. At a stagnation point the
transport term vanishes, so Eulerian and material tangents agree.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialNavierStokesTangent

open scoped BigOperators Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeCoefficientLimitEquation PancakeInfinitePressureHessian PancakeInfiniteSpatialPressure
open PancakeLocalGradientEquation PancakeSpatialGradientDifferentiation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

theorem gradient_infiniteVelocityRHS (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialVelocityGradient (fullFourierField id (infiniteVelocityRHS nu u)) x =
      -matrixTransport (fullFourierField id u)
          (spatialVelocityGradient (fullFourierField id u)) x -
        spatialVelocityGradient (fullFourierField id u) x *
          spatialVelocityGradient (fullFourierField id u) x -
        spatialHessian (spatialPressure u) x +
        (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (fullFourierField id u)) x := by
  ext i j
  have h := congrFun (coordinateDerivative_velocityRHS_eq nu u hu hd j x) i
  simpa only [gradientProduct_eq_matrixSquare, spatialVelocityGradient, matrixTransport,
    matrixLaplacian, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply] using h

theorem matrixTransport_eq_zero (u : T3 → VelocityCoefficient) (A : T3 → M3)
    (x : T3) (hx : u x = 0) : matrixTransport u A x = 0 := by
  ext i j
  simp [matrixTransport, spatialTransport, hx]

theorem gradient_infiniteVelocityRHS_of_stagnation (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (x : T3) (hx : fullFourierField id u x = 0) :
    spatialVelocityGradient (fullFourierField id (infiniteVelocityRHS nu u)) x =
      -(spatialVelocityGradient (fullFourierField id u) x *
          spatialVelocityGradient (fullFourierField id u) x) -
        spatialHessian (spatialPressure u) x +
        (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (fullFourierField id u)) x := by
  rw [gradient_infiniteVelocityRHS nu u hu hd x, matrixTransport_eq_zero _ _ x hx,
    neg_zero, zero_sub]

end Mettapedia.FluidDynamics.NavierStokes.SpatialNavierStokesTangent
