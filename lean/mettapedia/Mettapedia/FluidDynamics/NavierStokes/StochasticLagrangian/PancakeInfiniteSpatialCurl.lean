import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeIndexedFourierMoments
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHaarTransportRate

/-!
# Actual spatial curl of an infinite Fourier field

Curl is defined using ordinary derivatives of coordinate translations,
not by prescribing its Fourier coefficients. An absolute first moment
justifies the identification with the termwise curl series.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialCurl

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeCurlOutputTail

local notation "T3" => UnitAddTorus (Fin 3)

variable {ι : Type*}

def coordinateDerivative (f : T3 → VelocityCoefficient) (j : Fin 3) (x : T3) : VelocityCoefficient :=
  deriv (fun h : ℝ ↦ f (x + coordinateShift j h)) 0

def spatialCurl (f : T3 → VelocityCoefficient) (x : T3) : VelocityCoefficient :=
  ![coordinateDerivative f 1 x 2 - coordinateDerivative f 2 x 1,
    coordinateDerivative f 2 x 0 - coordinateDerivative f 0 x 2,
    coordinateDerivative f 0 x 1 - coordinateDerivative f 1 x 0]

theorem coordinateDerivative_fullFourierField (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (indexedFirstMoment freq a)) (j : Fin 3) (x : T3) :
    coordinateDerivative (fullFourierField freq a) j x =
      fullFourierField freq (indexedDerivativeCoeff freq j a) x := by
  simpa only [coordinateDerivative, coordinateShift_zero, add_zero] using
    (hasDerivAt_fullFourierField_shift freq a (summable_norm_coefficients freq a ha) j
      (summable_norm_derivativeCoefficients freq a ha j) 0 x).deriv

theorem summable_pointwise_modes (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun n ↦ ‖a n‖)) (x : T3) :
    Summable (fun n ↦ UnitAddTorus.mFourier (freq n) x • a n) :=
  (ContinuousMap.evalCLM (R := ℂ) (M := VelocityCoefficient) x).summable
    (summable_modeField freq a ha)

theorem fullFourierField_component (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun n ↦ ‖a n‖)) (x : T3) (i : Fin 3) :
    fullFourierField freq a x i = ∑' n, UnitAddTorus.mFourier (freq n) x * a n i := by
  rw [fullFourierField_apply freq a ha, tsum_apply (summable_pointwise_modes freq a ha x)]
  rfl

theorem spatialCurl_fullFourierField (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (indexedFirstMoment freq a)) :
    spatialCurl (fullFourierField freq a) = fullFourierField freq (indexedCurlCoeff freq a) := by
  have hd (j : Fin 3) := summable_norm_derivativeCoefficients freq a ha j
  have hc := summable_norm_curlCoefficients freq a ha
  have hs (j i : Fin 3) (x : T3) :
      Summable (fun n ↦ UnitAddTorus.mFourier (freq n) x * indexedDerivativeCoeff freq j a n i) :=
    Pi.summable.mp (summable_pointwise_modes freq (indexedDerivativeCoeff freq j a) (hd j) x) i
  funext x i
  unfold spatialCurl
  simp only [coordinateDerivative_fullFourierField freq a ha]
  fin_cases i <;>
    simp [
      fullFourierField_component freq (indexedDerivativeCoeff freq _ a) (hd _) x,
      fullFourierField_component freq (indexedCurlCoeff freq a) hc x]
  all_goals
    rw [← (hs _ _ x).tsum_sub (hs _ _ x)]
    apply tsum_congr
    intro n
    simp [indexedDerivativeCoeff, indexedCurlCoeff, coefficientCross, wavevectorCoefficient,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem spatialCurl_velocity (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    spatialCurl (fullFourierField id u) = fullFourierField id (PancakeGalerkinKineticEnergy.fourierCurl u) := by
  exact spatialCurl_fullFourierField id u (by simpa only [indexedFirstMoment_id] using hu)

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialCurl
