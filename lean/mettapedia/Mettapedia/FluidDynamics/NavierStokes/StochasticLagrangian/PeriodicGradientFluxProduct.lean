import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxPair
import Mettapedia.Analysis.BilinearSeries

/-!
# Gradient projection of actual periodic tensor products

Absolutely convergent Fourier products identify the physical tensor with
the pair-indexed series before applying the fixed gradient projection.
The vorticity-gradient specialization uses derivatives of the same
infinite Fourier field, rather than independent formal coefficients.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxProduct

open scoped ComplexConjugate
open Mettapedia.Analysis UnitTorusGradientProjection ContinuousFieldBilinear
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative PancakeInfiniteFourierProduct
open PancakeInfiniteRealCurl PancakeInfiniteSpatialCurl PancakePhysicalFourierDerivative
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeHigherDerivativeMoments PancakeIndexedFourierMoments PancakeCurlOutputTail
open PancakeLocalStrainReality PancakeGalerkinKineticEnergy LongitudinalVorticityTime
open LocalWeightedCurlCancellation LocalSpatialVorticityJets
open PeriodicGradientFluxSymbol

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def coordinateSmul (j : Fin 3) : VelocityCoefficient →L[ℂ] VelocityCoefficient →L[ℂ] VelocityCoefficient :=
  (ContinuousLinearMap.lsmul ℂ ℂ).comp (ContinuousLinearMap.proj j)

def pairCoeff (a b : FourierVelocity) (j : Fin 3) (p : Wavevector × Wavevector) : VelocityCoefficient :=
  a p.1 j • b p.2

theorem summable_norm_pairCoeff (a b : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) (j : Fin 3) :
    Summable (fun p ↦ ‖pairCoeff a b j p‖) :=
  BilinearSeries.summable_norm_apply (coordinateSmul j) a b ha hb

theorem fullFourierField_pairCoeff (a b : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖)) (j : Fin 3) (x : T3) :
    fullFourierField pairFrequency (pairCoeff a b j) x =
      fullFourierField id a x j • fullFourierField id b x := by
  have hna : Summable (fun k ↦ ‖UnitAddTorus.mFourier k x • a k‖) := by
    simpa only [norm_smul, norm_character, one_mul] using ha
  have hnb : Summable (fun k ↦ ‖UnitAddTorus.mFourier k x • b k‖) := by
    simpa only [norm_smul, norm_character, one_mul] using hb
  have he := (BilinearSeries.hasSum_apply (coordinateSmul j)
    (fun k ↦ UnitAddTorus.mFourier k x • a k)
    (fun k ↦ UnitAddTorus.mFourier k x • b k) hna hnb).tsum_eq
  have hmode (p : Wavevector × Wavevector) :
      coordinateSmul j (UnitAddTorus.mFourier p.1 x • a p.1)
        (UnitAddTorus.mFourier p.2 x • b p.2) =
      UnitAddTorus.mFourier (pairFrequency p) x • pairCoeff a b j p := by
    change (UnitAddTorus.mFourier p.1 x * a p.1 j) •
      (UnitAddTorus.mFourier p.2 x • b p.2) = _
    simp only [pairFrequency, pairCoeff, UnitAddTorus.mFourier_add, smul_smul]
    congr 1
    ring
  simp_rw [hmode] at he
  rw [fullFourierField_apply pairFrequency _ (summable_norm_pairCoeff a b ha hb j),
    fullFourierField_apply id a ha, fullFourierField_apply id b hb]
  exact he

def productField (a b : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  pointwise (ContinuousLinearMap.lsmul ℝ ℝ) (componentField j (realField a)) (realField b)

theorem productField_eq_pairField (a b : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hr : ∀ n, a (-n) = coefficientConjugate (a n)) (j : Fin 3) :
    productField a b j = (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
      (fullFourierField pairFrequency (pairCoeff a b j)) := by
  ext x i
  have hi := fullFourierField_im_zero a ha hr x j
  change ((fullFourierField id a x j).re * (fullFourierField id b x i).re) =
    (fullFourierField pairFrequency (pairCoeff a b j) x i).re
  rw [fullFourierField_pairCoeff a b ha hb]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, hi, zero_mul, sub_zero]

theorem gradientProjection_productField (a b : FourierVelocity)
    (ha : Summable (fun n ↦ ‖a n‖)) (hb : Summable (fun n ↦ ‖b n‖))
    (hr : ∀ n, a (-n) = coefficientConjugate (a n)) :
    gradientProjection (toTensorL2 (productField a b)) =
      ∑' p : Wavevector × Wavevector, toTensorL2 (fun j ↦
        realMode (p.1 + p.2) (projectedCoeff (p.1 + p.2) (fun l ↦ pairCoeff a b l p) j)) := by
  have he : productField a b = fun j ↦ (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
      (fullFourierField pairFrequency (pairCoeff a b j)) :=
    funext (productField_eq_pairField a b ha hb hr)
  rw [he]
  exact gradientProjection_indexedFourier pairFrequency (pairCoeff a b)
    (summable_norm_pairCoeff a b ha hb)

/-- A single coordinate contribution to the actual viscous flux tensor. -/
def curlGradientProduct (u : FourierVelocity) (r : Fin 3) (j : Fin 3) : C(T3, R3) :=
  productField (indexedDerivativeCoeff id r (fourierCurl u))
    (indexedDerivativeCoeff id r (fourierCurl u)) j

theorem curlGradientProduct_apply (u : FourierVelocity) (r j : Fin 3) (x : T3) :
    curlGradientProduct u r j x =
      fullCurlGradient u r x j • fullCurlGradient u r x := rfl

theorem gradientProjection_curlGradientProduct (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) (r : Fin 3) :
    gradientProjection (toTensorL2 (curlGradientProduct u r)) =
      ∑' p : Wavevector × Wavevector, toTensorL2 (fun j ↦ realMode (p.1 + p.2)
        (projectedCoeff (p.1 + p.2) (fun l ↦
          pairCoeff (indexedDerivativeCoeff id r (fourierCurl u))
            (indexedDerivativeCoeff id r (fourierCurl u)) l p) j)) := by
  have hw : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu
  exact gradientProjection_productField _ _
    (summable_norm_derivativeCoefficients id _ hw r)
    (summable_norm_derivativeCoefficients id _ hw r)
    (indexedDerivativeCoeff_conjugate _ (fourierCurl_real u hr) r)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxProduct
