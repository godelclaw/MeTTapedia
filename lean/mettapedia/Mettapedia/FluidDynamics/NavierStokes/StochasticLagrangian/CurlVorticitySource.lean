import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialCurlCurl
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CurlEigenfieldDefect

/-!
# The actual material source of curl vorticity

Double curl removes the Leray projection, but it does not remove the
gradient-divergence part of nonlinear advection. This term is identified with
the gradient of the pressure Laplacian. The cross-derivative terms in material
transport are retained explicitly; no bound on their accumulated size is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CurlVorticitySource

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeInfiniteSpatialLaplacian PancakeSpatialGradientDifferentiation
open PancakeInfiniteSpatialPressure PancakeLocalProjectedEquation PancakeInfinitePressurePoisson
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge PancakePeriodicVorticityEquation
open PancakePeriodicComplexStretch
open PancakeCoefficientLimitEquation PancakeInfiniteVelocityEnvelope PancakePhysicalConvectionCoefficients
open PancakeInfiniteDirectionalTransport PancakeDyadicDirectionEvolution
open LocalWeightedCurlCancellation LocalVorticityNegation LocalHelicityCenterEvolution
open VelocityRHSMoments SpatialTransportLaplacian SpatialCurlCurl

local notation "T3" => UnitAddTorus (Fin 3)

/-- Fourier coefficients of the full nonlinear advection, before projection. -/
def advectionCoeff (u : FourierVelocity) : FourierVelocity :=
  fun q ↦ unitTorusDerivativePhase • infiniteConvection u q

theorem summable_fourierMoment_advectionCoeff (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) :
    Summable (fourierMoment m (advectionCoeff u)) := by
  apply CurlEigenfieldDefect.summable_fourierMoment_smul
  exact ((summable_convolutionEnvelope _ (fourierMoment_nonneg _ _) hu).mul_left 3).of_nonneg_of_le
    (fourierMoment_nonneg _ _)
    (fourierMoment_infiniteConvection_le m u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))

theorem curl_inviscidRHS (u : FourierVelocity) :
    fourierCurl (infiniteVelocityRHS 0 u) = -fourierCurl (advectionCoeff u) := by
  funext q
  simp only [fourierCurl, infiniteVelocityRHS, unitTorusViscousVorticityCoeff,
    Complex.ofReal_zero, zero_mul, zero_smul, add_zero, cross_leray]
  ext i
  fin_cases i <;> simp [fourierCurl, advectionCoeff, coefficientCross] <;> ring

theorem doubleCurl_inviscidRHS (u : FourierVelocity) :
    fourierCurl (fourierCurl (infiniteVelocityRHS 0 u)) =
      -fourierCurl (fourierCurl (advectionCoeff u)) := by
  rw [curl_inviscidRHS, fourierCurl_neg]

/-- Pressure remains visible after the projection is removed. -/
theorem fullFourierField_doubleCurl_inviscidRHS (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    fullFourierField id (fourierCurl (fourierCurl (infiniteVelocityRHS 0 u))) x =
      spatialLaplacian (spatialAdvection (fullFourierField id u)) x -
        spatialGradient (spatialDivergence (spatialAdvection (fullFourierField id u))) x := by
  rw [doubleCurl_inviscidRHS, fullFourierField_neg, ContinuousMap.neg_apply,
    fullFourierField_doubleCurl _ (summable_fourierMoment_advectionCoeff 2 u hu)]
  have ha : (fullFourierField id (advectionCoeff u) : T3 → VelocityCoefficient) =
      spatialAdvection (fullFourierField id u) :=
    fullFourierField_advection u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu) hd
  rw [ha]
  abel

theorem spatialTransport_neg_left (u v : T3 → VelocityCoefficient) (x : T3) :
    spatialTransport (-u) v x = -spatialTransport u v x := by
  simp [spatialTransport]

theorem spatialTransport_neg_right (u v : T3 → VelocityCoefficient) (x : T3) :
    spatialTransport u (-v) x = -spatialTransport u v x := by
  simp only [spatialTransport, coordinateDerivative_neg, smul_neg, Finset.sum_neg_distrib]

theorem gradient_neg (f : T3 → ℂ) (x : T3) :
    spatialGradient (-f) x = -spatialGradient f x := by
  ext i
  exact deriv.fun_neg

theorem gradient_pressureLaplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialGradient (scalarLaplacian (spatialPressure u)) x =
      -spatialGradient (spatialDivergence (spatialAdvection (fullFourierField id u))) x := by
  have hp : scalarLaplacian (spatialPressure u) =
      -spatialDivergence (spatialAdvection (fullFourierField id u)) :=
    funext (spatialPressure_poisson u hu hd)
  rw [hp, gradient_neg]

/-- The cross-derivative and pressure source left after material transport
and the common velocity-gradient action have been separated. -/
def spatialSource (u : FourierVelocity) (x : T3) : VelocityCoefficient :=
  2 • (∑ j : Fin 3, spatialTransport (fullFourierField id (indexedDerivativeCoeff id j u))
    (fullFourierField id (indexedDerivativeCoeff id j u)) x) +
      spatialGradient (scalarLaplacian (spatialPressure u)) x

theorem doubleCurl_material_inviscid (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (x : T3) (hr : ∀ i, ((fullFourierField id u x i).re : ℂ) = fullFourierField id u x i) :
    fullFourierField id (fourierCurl (fourierCurl (infiniteVelocityRHS 0 u))) x +
      fullFourierField id (directionalCoeff (fourierCurl (fourierCurl u))
        (fun i ↦ (fullFourierField id u x i).re)) x =
      -spatialTransport (fullFourierField id (fourierCurl (fourierCurl u)))
        (fullFourierField id u) x + spatialSource u x := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hb : (fullFourierField id (fourierCurl (fourierCurl u)) : T3 → VelocityCoefficient) =
      -spatialLaplacian (fullFourierField id u) := by
    funext y
    rw [fourierCurl_fourierCurl_eq_neg_laplacian u hd]
    exact fullFourierField_negativeLaplacian_eq u hu2 y
  rw [fullFourierField_doubleCurl_inviscidRHS u hu hd,
    fullFourierField_directionalCoeff_transport _
      (summable_fourierMoment_curl 1 _ (summable_fourierMoment_curl 2 u hu3)) _ x hr]
  change spatialLaplacian (spatialTransport (fullFourierField id u) (fullFourierField id u)) x -
      spatialGradient (spatialDivergence (spatialAdvection (fullFourierField id u))) x + _ = _
  rw [hb, spatialTransport_neg_left, spatialTransport_neg_right, laplacian_transport u u hu2 hu3]
  unfold spatialSource
  rw [gradient_pressureLaplacian u hu2 hd]
  abel

end Mettapedia.FluidDynamics.NavierStokes.CurlVorticitySource
