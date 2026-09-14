import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxProjectedEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicProjectedTensorDiffusion

/-!
# Ordinary spatial diffusion of the cubic stretching flux

The second derivatives are constructed from the actual Fourier fields.
Their product rule isolates the full Laplacian and the mixed derivative
cost in the viscous material source, with its exact coefficient and sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxSpatialDiffusion

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution
open PancakeInfiniteRealCurl PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeFourierTranslationCurve PancakeHaarTransportRate LocalWeightedCurlCancellation
open LocalJointDiffusionBudget LongitudinalVorticityTime FullLambVector LongitudinalGradientFlux
open LocalStretchingFluxTime StretchingFluxMaterialRate StretchingFluxProjectedEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def velocityThirdDerivativeField (u : FourierVelocity) (j k : Fin 3) : C(T3, R3) :=
  realField (indexedDerivativeCoeff id k (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j u)))

def vorticitySecondDerivativeField (u : FourierVelocity) (k : Fin 3) : C(T3, R3) :=
  realField (indexedDerivativeCoeff id k (indexedDerivativeCoeff id k (fourierCurl u)))

def stretchingSecondDerivativeField (u : FourierVelocity) (k : Fin 3) : C(T3, R3) :=
  (∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocityThirdDerivativeField u j k) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticitySecondDerivativeField u k)) (velocityDerivativeField u j))) +
  (2 : ℝ) • ∑ j, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (LongitudinalVorticityTime.gradientField u k)) (velocitySecondDerivativeField u j k)

def fluxSecondDerivativeField (u : FourierVelocity) (j k : Fin 3) : C(T3, R3) :=
  -(pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (vorticityField u)) (stretchingSecondDerivativeField u k) +
    pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (vorticitySecondDerivativeField u k)) (stretchingField u) +
    (2 : ℝ) • pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (LongitudinalVorticityTime.gradientField u k)) (stretchingGradientField u k))

def fluxLaplacianField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ∑ k, fluxSecondDerivativeField u j k

def viscousCrossField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ∑ k, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (LongitudinalVorticityTime.gradientField u k)) (stretchingGradientField u k) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField u))
        (∑ r, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
          (componentField r (LongitudinalVorticityTime.gradientField u k)) (velocitySecondDerivativeField u r k)))

theorem hasDerivAt_stretchingGradientField_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ stretchingGradientField u k (x + coordinateShift k t))
      (stretchingSecondDerivativeField u k (x + coordinateShift k h)) h := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hw : HasDerivAt (fun t ↦ vorticityField u (x + coordinateShift k t))
      (LongitudinalVorticityTime.gradientField u k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift (fourierCurl u)
      (summable_fourierMoment_curl 1 u hu2) k x h using 1
  have hdw : HasDerivAt (fun t ↦ LongitudinalVorticityTime.gradientField u k (x + coordinateShift k t))
      (vorticitySecondDerivativeField u k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift (indexedDerivativeCoeff id k (fourierCurl u))
      (summable_fourierMoment_derivative 1 _ (summable_fourierMoment_curl 2 u hu) k) k x h using 1
  have ha (j : Fin 3) : HasDerivAt (fun t ↦ velocityDerivativeField u j (x + coordinateShift k t))
      (velocitySecondDerivativeField u j k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift (indexedDerivativeCoeff id j u)
      (summable_fourierMoment_derivative 1 u hu2 j) k x h using 1
  have hda (j : Fin 3) : HasDerivAt (fun t ↦ velocitySecondDerivativeField u j k (x + coordinateShift k t))
      (velocityThirdDerivativeField u j k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift
      (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j u))
      (summable_fourierMoment_derivative 1 _ (summable_fourierMoment_derivative 2 u hu j) k) k x h using 1
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
    (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hw).smul (hda j)).add
      (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hdw).smul (ha j)))
  convert! hh using 1
  ext i
  simp only [stretchingSecondDerivativeField, pointwise, ContinuousMap.coe_mk,
    ContinuousLinearMap.lsmul_apply, componentField_apply, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hp (j : Fin 3) (v : R3) : (EuclideanSpace.proj j) v = v j := rfl
  simp only [Function.comp_def, hp]
  ring

theorem hasDerivAt_fluxGradientField_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ fluxGradientField u j k (x + coordinateShift k t))
      (fluxSecondDerivativeField u j k (x + coordinateShift k h)) h := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hw : HasDerivAt (fun t ↦ vorticityField u (x + coordinateShift k t))
      (LongitudinalVorticityTime.gradientField u k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift (fourierCurl u)
      (summable_fourierMoment_curl 1 u hu2) k x h using 1
  have hdw : HasDerivAt (fun t ↦ LongitudinalVorticityTime.gradientField u k (x + coordinateShift k t))
      (vorticitySecondDerivativeField u k (x + coordinateShift k h)) h := by
    convert! hasDerivAt_realFullField_shift (indexedDerivativeCoeff id k (fourierCurl u))
      (summable_fourierMoment_derivative 1 _ (summable_fourierMoment_curl 2 u hu) k) k x h using 1
  have hh := ((((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hw).smul
    (hasDerivAt_stretchingGradientField_shift u hu k x h)).add
      (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hdw).smul
        (hasDerivAt_stretchingField_shift u hu2 k x h))).neg
  convert! hh using 1
  ext i
  simp only [fluxSecondDerivativeField, pointwise, ContinuousMap.coe_mk,
    ContinuousLinearMap.lsmul_apply, componentField_apply, ContinuousMap.add_apply,
    ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  have hp (j : Fin 3) (v : R3) : (EuclideanSpace.proj j) v = v j := rfl
  simp only [Function.comp_def, hp]
  ring

/-- The displayed Laplacian consists of ordinary iterated derivatives. -/
theorem fluxLaplacianField_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    fluxLaplacianField u j x =
      ∑ k, deriv (deriv (fun t ↦ fluxField 0 u j (x + coordinateShift k t))) 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  simp only [fluxLaplacianField, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have he : deriv (fun t ↦ fluxField 0 u j (x + coordinateShift k t)) =
      fun h ↦ fluxGradientField u j k (x + coordinateShift k h) :=
    funext (fun h ↦ (hasDerivAt_fluxField_shift u hu2 j k x h).deriv)
  rw [he]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_fluxGradientField_shift u hu j k x 0).deriv.symm

theorem sum_vorticitySecondDerivativeField (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    (∑ k, vorticitySecondDerivativeField u k x) = fullVorticityLaplacian u x :=
  sum_fullCurlSecond u hu x

theorem sum_velocityThirdDerivativeField (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) :
    (∑ k, velocityThirdDerivativeField u j k x) =
      complexRealPartEuclideanCLM (spatialLaplacian
        (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x) := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  simp only [coordinateDerivative_fullFourierField id u hm]
  simp only [spatialLaplacian, coordinateDerivative2_fullFourierField _
    (summable_fourierMoment_derivative 2 u hu j), map_sum]
  rfl

/-- Viscosity produces the full flux Laplacian plus an explicit mixed cost. -/
theorem fluxMaterialRateField_eq_laplacian_add_cross (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (j : Fin 3) :
    fluxMaterialRateField ν u j = fluxMaterialRateField 0 u j +
      ν • (fluxLaplacianField u j + (2 : ℝ) • viscousCrossField u j) := by
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
    fluxMaterialRateField_apply ν u hu hd hr, fluxMaterialRateField_apply 0 u hu hd hr,
    stretchingDiffusion, ← sum_vorticitySecondDerivativeField u hu x]
  simp_rw [← sum_velocityThirdDerivativeField u hu _ x]
  ext i
  simp only [fluxLaplacianField, fluxSecondDerivativeField, stretchingSecondDerivativeField,
    viscousCrossField, pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply,
    componentField_apply, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    velocityDerivativeField_apply]
  ring

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxSpatialDiffusion
