import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBlockReality

/-!
# Reality and actual real spatial curl

Conjugate-symmetric coefficients reconstruct a real field. Real part
commutes with the actual coordinate derivatives when these derivatives
exist. This gives a real, derivative-defined curl for the full fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteRealCurl

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeInfiniteSpatialCurl
open PancakeInfiniteFourierProduct PancakeCurlOutputTail PancakeBlockReality
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def realFullField (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (fullFourierField id u x)

def realCoordinateDerivative (f : T3 → R3) (j : Fin 3) (x : T3) : R3 :=
  deriv (fun h : ℝ ↦ f (x + coordinateShift j h)) 0

def realSpatialCurl (f : T3 → R3) (x : T3) : R3 :=
  WithLp.toLp 2 ![realCoordinateDerivative f 1 x 2 - realCoordinateDerivative f 2 x 1,
    realCoordinateDerivative f 2 x 0 - realCoordinateDerivative f 0 x 2,
    realCoordinateDerivative f 0 x 1 - realCoordinateDerivative f 1 x 0]

def realCross (v w : R3) : R3 := WithLp.toLp 2 (crossProduct (fun i ↦ v i) (fun i ↦ w i))

theorem fullFourierField_conj (u : FourierVelocity) (hu : Summable (fun k ↦ ‖u k‖))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) (i : Fin 3) :
    conj (fullFourierField id u x i) = fullFourierField id u x i := by
  rw [fullFourierField_component id u hu, Complex.conj_tsum]
  calc
    _ = ∑' k, UnitAddTorus.mFourier (-k) x * u (-k) i := by
      apply tsum_congr
      intro k
      simp [UnitAddTorus.mFourier_neg, hr, coefficientConjugate]
    _ = _ := (Equiv.neg Wavevector).tsum_eq (fun k ↦ UnitAddTorus.mFourier k x * u k i)

theorem fullFourierField_im_zero (u : FourierVelocity) (hu : Summable (fun k ↦ ‖u k‖))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) (i : Fin 3) :
    (fullFourierField id u x i).im = 0 := by
  have h := congrArg Complex.im (fullFourierField_conj u hu hr x i)
  simp only [Complex.conj_im] at h
  linarith

theorem realCoordinateDerivative_realPart (f : T3 → VelocityCoefficient)
    (j : Fin 3) (x : T3) (hf : DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0) :
    realCoordinateDerivative (fun y ↦ complexRealPartEuclideanCLM (f y)) j x =
      complexRealPartEuclideanCLM (coordinateDerivative f j x) :=
  (complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv

theorem realSpatialCurl_realPart (f : T3 → VelocityCoefficient)
    (hf : ∀ j x, DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0) :
    realSpatialCurl (fun x ↦ complexRealPartEuclideanCLM (f x)) =
      fun x ↦ complexRealPartEuclideanCLM (spatialCurl f x) := by
  funext x
  ext i
  unfold realSpatialCurl
  simp only [realCoordinateDerivative_realPart f _ x (hf _ x)]
  fin_cases i <;> simp [spatialCurl, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

theorem differentiableAt_fullFourierField_shift {ι : Type*} (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (ha : Summable (indexedFirstMoment freq a)) (j : Fin 3) (x : T3) :
    DifferentiableAt ℝ (fun h ↦ fullFourierField freq a (x + coordinateShift j h)) 0 :=
  (hasDerivAt_fullFourierField_shift freq a (summable_norm_coefficients freq a ha) j
    (summable_norm_derivativeCoefficients freq a ha j) 0 x).differentiableAt

theorem realSpatialCurl_realFullField (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    realSpatialCurl (realFullField u) = realFullField (PancakeGalerkinKineticEnergy.fourierCurl u) := by
  unfold realFullField
  rw [realSpatialCurl_realPart _ (differentiableAt_fullFourierField_shift id u
    (by simpa only [indexedFirstMoment_id] using hu)), spatialCurl_velocity u hu]

theorem realPart_cross (v w : VelocityCoefficient) (hv : ∀ i, (v i).im = 0) :
    complexRealPartEuclideanCLM (coefficientCross v w) =
      realCross (complexRealPartEuclideanCLM v) (complexRealPartEuclideanCLM w) := by
  ext i
  fin_cases i <;> simp [realCross, cross_apply, coefficientCross, complexRealPartEuclideanCLM_apply,
    complexRealPartEuclidean, Complex.mul_re, hv]

theorem realCross_fullField (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) :
    realCross (realFullField u x) (realFullField v x) =
      complexRealPartEuclideanCLM (fullFourierField pairFrequency (crossPair u v) x) := by
  rw [← cross_fullFourierField u v hu hv x, realPart_cross _ _
    (fullFourierField_im_zero u (summable_norm_coefficients id u
      (by simpa only [indexedFirstMoment_id] using hu)) hr x)]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteRealCurl
