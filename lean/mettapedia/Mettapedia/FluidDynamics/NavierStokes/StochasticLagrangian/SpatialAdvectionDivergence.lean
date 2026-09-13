import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CurlVorticitySource

/-!
# Divergence of actual incompressible advection

The divergence of nonlinear advection is the trace of the square of the
velocity gradient. Its ordinary spatial derivative is obtained from the
second Fourier moment. This keeps pressure elimination at the level of
proved local differential identities.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialAdvectionDivergence

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeSpatialGradientDifferentiation PancakePhysicalConvectionCoefficients
open PancakeInfiniteSpatialPressure PancakeLocalProjectedEquation PancakeLocalGradientEquation
open PancakeFourierTranslationCurve SpatialTransportLaplacian SpatialCurlCurl
open PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)

theorem divergence_advection (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialDivergence (spatialAdvection (fullFourierField id u)) x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        coordinateDerivative (fullFourierField id u) i x j *
          coordinateDerivative (fullFourierField id u) j x i := by
  have hu1 := summable_firstMoment_of_second u hu
  have hdf (i : Fin 3) : (fullFourierField id (indexedDerivativeCoeff id i u) : T3 → VelocityCoefficient) =
      (fun y ↦ coordinateDerivative (fullFourierField id u) i y) :=
    (coordinateDerivative_fullFourierField_eq u hu1 i).symm
  have hz (j : Fin 3) :
      (∑ i : Fin 3, coordinateDerivative
        (fun y ↦ coordinateDerivative (fullFourierField id u) i y) j x i) = 0 := by
    rw [← gradient_divergence u hu]
    have hdiv : spatialDivergence (fullFourierField id u) = 0 :=
      funext (spatialDivergence_fullFourierField u hu hd)
    rw [hdiv]
    simp [spatialGradient, scalarCoordinateDerivative]
  have hs : (∑ i : Fin 3, ∑ j : Fin 3, fullFourierField id u x j *
      coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) i y) j x i) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hz, mul_zero, Finset.sum_const_zero]
  change (∑ i : Fin 3, coordinateDerivative
    (spatialTransport (fullFourierField id u) (fullFourierField id u)) i x i) = _
  simp only [coordinateDerivative_transport u u hu1 hu, Pi.add_apply, spatialTransport,
    hdf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [hs, add_zero]

theorem divergence_advection_eq_trace (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialDivergence (spatialAdvection (fullFourierField id u)) x =
      ((spatialVelocityGradient (fullFourierField id u) x) *
        (spatialVelocityGradient (fullFourierField id u) x)).trace := by
  rw [divergence_advection u hu hd]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, spatialVelocityGradient]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem gradient_divergence_advection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) (k : Fin 3) :
    spatialGradient (spatialDivergence (spatialAdvection (fullFourierField id u))) x k =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) i y) k x j *
            coordinateDerivative (fullFourierField id u) j x i +
          coordinateDerivative (fullFourierField id u) i x j *
            coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) k x i) := by
  have h (i j : Fin 3) :=
    ((hasDerivAt_pi.mp (hasDerivAt_coordinateDerivative_shift_zero u hu i k x)) j).mul
      ((hasDerivAt_pi.mp (hasDerivAt_coordinateDerivative_shift_zero u hu j k x)) i)
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h i j))).deriv
  simp only [coordinateShift_zero, add_zero] at hh
  simp only [spatialGradient, scalarCoordinateDerivative, divergence_advection u hu hd]
  exact hh

end Mettapedia.FluidDynamics.NavierStokes.SpatialAdvectionDivergence
