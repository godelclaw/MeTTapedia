import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteSpatialCurl
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Products of actual infinite Fourier fields

Absolute first moments control the first moment of the pair-indexed
cross-product series. Continuous bilinearity identifies its sum with the
pointwise product of the constructed fields by absolute double summation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierProduct

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeInfiniteFourierDerivative
open PancakeIndexedFourierMoments PancakeCurlOutputTail PancakeInfiniteSpatialCurl
open PancakeLowTouchEnergy PancakeTransverseEnergyFreezing

local notation "T3" => UnitAddTorus (Fin 3)

def pairFrequency (p : Wavevector × Wavevector) : Wavevector := p.1 + p.2

def crossPair (u v : FourierVelocity) (p : Wavevector × Wavevector) : VelocityCoefficient :=
  coefficientCross (u p.1) (v p.2)

theorem indexedFirstMoment_crossPair_le (u v : FourierVelocity) (p : Wavevector × Wavevector) :
    indexedFirstMoment pairFrequency (crossPair u v) p ≤ fourierMoment 1 u p.1 * fourierMoment 1 v p.2 := by
  have hf : 1 + ‖frequencyVec (p.1 + p.2)‖ ≤
      (1 + ‖frequencyVec p.1‖) * (1 + ‖frequencyVec p.2‖) := by
    rw [frequencyVec_add]
    have h := norm_add_le (frequencyVec p.1) (frequencyVec p.2)
    nlinarith [mul_nonneg (norm_nonneg (frequencyVec p.1)) (norm_nonneg (frequencyVec p.2))]
  calc
    _ ≤ ((1 + ‖frequencyVec p.1‖) * (1 + ‖frequencyVec p.2‖)) *
        (‖coefficientVec (u p.1)‖ * ‖coefficientVec (v p.2)‖) :=
      mul_le_mul hf (norm_complex_cross_le _ _) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [fourierMoment, pow_one]; ring

theorem summable_firstMoment_crossPair (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    Summable (indexedFirstMoment pairFrequency (crossPair u v)) :=
  Summable.of_nonneg_of_le (indexedFirstMoment_nonneg _ _) (indexedFirstMoment_crossPair_le u v)
    (hu.mul_of_nonneg hv (fourierMoment_nonneg _ _) (fourierMoment_nonneg _ _))

theorem cross_tsum_right {ι : Type*} (a : VelocityCoefficient) (b : ι → VelocityCoefficient)
    (hb : Summable b) : coefficientCross a (∑' n, b n) = ∑' n, coefficientCross a (b n) :=
  (crossProduct (R := ℂ) a).toContinuousLinearMap.map_tsum hb

theorem cross_tsum_left {ι : Type*} (a : ι → VelocityCoefficient) (b : VelocityCoefficient)
    (ha : Summable a) : coefficientCross (∑' n, a n) b = ∑' n, coefficientCross (a n) b :=
  ((crossProduct (R := ℂ)).flip b).toContinuousLinearMap.map_tsum ha

theorem cross_mode_product (u v : FourierVelocity) (k l : Wavevector) (x : T3) :
    coefficientCross (UnitAddTorus.mFourier k x • u k) (UnitAddTorus.mFourier l x • v l) =
      UnitAddTorus.mFourier (k + l) x • crossPair u v (k, l) := by
  change crossProduct (UnitAddTorus.mFourier k x • u k) (UnitAddTorus.mFourier l x • v l) = _
  rw [(crossProduct (R := ℂ)).map_smul, LinearMap.smul_apply, map_smul, smul_smul]
  rw [UnitAddTorus.mFourier_add]
  rfl

theorem cross_fullFourierField (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (x : T3) :
    coefficientCross (fullFourierField id u x) (fullFourierField id v x) =
      fullFourierField pairFrequency (crossPair u v) x := by
  have hu' := summable_norm_coefficients id u (by simpa only [indexedFirstMoment_id] using hu)
  have hv' := summable_norm_coefficients id v (by simpa only [indexedFirstMoment_id] using hv)
  have hp := summable_norm_coefficients pairFrequency (crossPair u v) (summable_firstMoment_crossPair u v hu hv)
  rw [fullFourierField_apply id u hu', fullFourierField_apply id v hv',
    fullFourierField_apply pairFrequency (crossPair u v) hp,
    (summable_pointwise_modes pairFrequency (crossPair u v) hp x).tsum_prod,
    cross_tsum_left _ _ (summable_pointwise_modes id u hu' x)]
  apply tsum_congr
  intro k
  rw [cross_tsum_right _ _ (summable_pointwise_modes id v hv' x)]
  apply tsum_congr
  intro l
  exact cross_mode_product u v k l x

theorem spatialCurl_cross_fullFourierField (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    spatialCurl (fun x ↦ coefficientCross (fullFourierField id u x) (fullFourierField id v x)) =
      fullFourierField pairFrequency (curlPair u v) := by
  have he : (fun x ↦ coefficientCross (fullFourierField id u x) (fullFourierField id v x)) =
      fullFourierField pairFrequency (crossPair u v) := funext (cross_fullFourierField u v hu hv)
  rw [he]
  exact spatialCurl_fullFourierField pairFrequency (crossPair u v) (summable_firstMoment_crossPair u v hu hv)

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierProduct
