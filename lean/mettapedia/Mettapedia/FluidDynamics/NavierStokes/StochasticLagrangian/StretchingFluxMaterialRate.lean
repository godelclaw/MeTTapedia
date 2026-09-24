import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStretchingFluxTime

/-!
# Pressure-resolved material rate of the stretching flux

All fields are built from the same Fourier velocity. The gradient remainder
is identified with the pressure Hessian and viscous Laplacian, and the
quadratic gradient terms cancel before any norm is taken.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxMaterialRate

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeVelocityGradientEnvelope PancakeInfiniteVelocityEnvelope
open PancakeTransverseEnergyFreezing PancakeGalerkinVorticityBridge
open PancakeInfiniteRealCurl PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian PancakeLocalGradientEquation
open PancakeSpatialGradientDifferentiation PancakeLocalStrainReality PancakeFourierTranslationCurve
open LocalVorticityTime LocalVorticityDiffusion LocalWeightedCurlCancellation LocalJointDiffusionBudget
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticitySeparation FullVorticityGradientTransport
open LongitudinalVorticityTime LongitudinalEnergyBalance FullLambVector LongitudinalGradientFlux
open LongitudinalProjectedTransport LocalStretchingFluxTime

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def velocitySecondDerivativeField (u : FourierVelocity) (j k : Fin 3) : C(T3, R3) :=
  realField (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j u))

def vorticityTransportField (u : FourierVelocity) : C(T3, R3) :=
  ∑ k, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField k (realField u)) (LongitudinalVorticityTime.gradientField u k)

def velocityGradientTransportField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ∑ k, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField k (realField u)) (velocitySecondDerivativeField u j k)

def gradientSquareField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ∑ k, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField k (velocityDerivativeField u j)) (velocityDerivativeField u k)

/-- This continuous field is proved below to be `-∂ⱼ∇p + νΔ∂ⱼu`. -/
def gradientRemainderField (ν : ℝ) (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  velocityDerivativeField (infiniteVelocityRHS ν u) j +
    velocityGradientTransportField u j + gradientSquareField u j

def vorticityDiffusionField (ν : ℝ) (u : FourierVelocity) : C(T3, R3) :=
  ν • realField (laplacianCoeff (fourierCurl u))

def stretchingTransportField (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocityGradientTransportField u j) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityTransportField u)) (velocityDerivativeField u j))

def stretchingMaterialRateField (ν : ℝ) (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (gradientRemainderField ν u j) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityDiffusionField ν u)) (velocityDerivativeField u j))

def fluxTransportField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  -(pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (stretchingTransportField u) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityTransportField u)) (stretchingField u))

def fluxMaterialRateField (ν : ℝ) (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  -pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (stretchingField u)) (stretchingField u) -
    pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (vorticityDiffusionField ν u)) (stretchingField u) -
    pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (vorticityField u)) (stretchingMaterialRateField ν u)

theorem realField_apply (u : FourierVelocity) (x : T3) :
    realField u x = realFullField u x := rfl

theorem velocitySecondDerivativeField_apply (u : FourierVelocity) (j k : Fin 3) (x : T3) :
    velocitySecondDerivativeField u j k x =
      complexRealPartEuclideanCLM
        (fullFourierField id (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j u)) x) := rfl

theorem gradientRemainderField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (j : Fin 3) (x : T3) :
    gradientRemainderField ν u j x =
      -complexRealPartEuclideanCLM (fun i ↦ spatialHessian (spatialPressure u) x i j) +
        ν • complexRealPartEuclideanCLM (spatialLaplacian
          (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using hu1
  have hmR : Summable (indexedFirstMoment id (infiniteVelocityRHS ν u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_velocityRHS ν u hu
  have hmD : Summable (indexedFirstMoment id (indexedDerivativeCoeff id j u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_derivative u hu2 j
  have him := fullFourierField_im_zero u (summable_norm_coefficients id u hm) hr x
  have hdIm (k : Fin 3) : (coordinateDerivative (fullFourierField id u) j x k).im = 0 := by
    rw [coordinateDerivative_fullFourierField id u hm]
    exact fullFourierField_im_zero _ (summable_norm_derivativeCoefficients id u hm j)
      (indexedDerivativeCoeff_conjugate u hr j) x k
  have he := congrArg complexRealPartEuclideanCLM
    (coordinateDerivative_velocityRHS_eq ν u hu hd j x)
  ext i
  have hei := congrArg (fun z : R3 ↦ z i) he
  simp only [gradientRemainderField, velocityGradientTransportField, gradientSquareField,
    ContinuousMap.add_apply, pointwise, ContinuousMap.coe_mk,
    ContinuousLinearMap.lsmul_apply, componentField_apply, velocityDerivativeField_apply,
    velocitySecondDerivativeField_apply, realField_apply, realFullField, velocityJet,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    PiLp.toLp_apply, Fin.sum_univ_three, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul]
  simp only [spatialTransport, gradientProduct, Finset.sum_apply,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.re_sum,
    Complex.ofReal_im, zero_mul, sub_zero, him,
    coordinateDerivative_fullFourierField id _ hmR,
    coordinateDerivative_fullFourierField id u hm] at hei
  simp only [coordinateDerivative_fullFourierField id u hm] at *
  simp only [coordinateDerivative_fullFourierField id _ hmD, hdIm, zero_mul, sub_zero,
    Fin.sum_univ_three] at hei
  linarith

theorem vorticityDiffusionField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    vorticityDiffusionField ν u x = ν • fullVorticityLaplacian u x := by
  rw [fullVorticityLaplacian, spatialCurl_velocity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu),
    spatialLaplacian_fullFourierField _ (summable_fourierMoment_curl 2 u hu)]
  rfl

theorem vorticity_materialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    vorticityField (infiniteVelocityRHS ν u) + vorticityTransportField u =
      stretchingField u + vorticityDiffusionField ν u := by
  apply ContinuousMap.ext
  intro x
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have he := vorticity_materialRate_eq_eulerian_add_transport ν u hu hd hr x
  rw [← gradient_vorticity, ← directional_velocityJet u hu1,
    fullVorticity_eq_realFullField u hu1] at he
  simpa only [ContinuousMap.add_apply, vorticityTransportField, ContinuousMap.sum_apply,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    stretchingField_apply, vorticityDiffusionField_apply ν u hu,
    vorticityField, realField_apply, LongitudinalVorticityTime.gradientField_apply] using he.symm

theorem stretching_materialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    stretchingRateField ν u + stretchingTransportField u = stretchingMaterialRateField ν u := by
  have hw := vorticity_materialRate_eq ν u hu hd hr
  have hw' : vorticityField (infiniteVelocityRHS ν u) =
      stretchingField u + vorticityDiffusionField ν u - vorticityTransportField u := by
    rw [← hw]
    abel
  ext x i
  simp only [stretchingRateField, stretchingTransportField, stretchingMaterialRateField,
    gradientRemainderField, hw', stretchingField, gradientSquareField,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem flux_materialRate_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (j : Fin 3) :
    fluxRateField ν u j + fluxTransportField u j = fluxMaterialRateField ν u j := by
  have hw := vorticity_materialRate_eq ν u hu hd hr
  have ha := stretching_materialRate_eq ν u hu hd hr
  have hw' : vorticityField (infiniteVelocityRHS ν u) =
      stretchingField u + vorticityDiffusionField ν u - vorticityTransportField u := by
    rw [← hw]; abel
  have ha' : stretchingRateField ν u = stretchingMaterialRateField ν u - stretchingTransportField u := by
    rw [← ha]; abel
  ext x i
  simp only [fluxRateField, fluxTransportField, fluxMaterialRateField, hw', ha',
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The actual pressure-Hessian action on vorticity. -/
def pressureAction (u : FourierVelocity) (x : T3) : R3 :=
  ∑ j, vorticityField u x j •
    complexRealPartEuclideanCLM (fun i ↦ spatialHessian (spatialPressure u) x i j)

/-- Both viscous product-rule contributions to the material stretching rate. -/
def stretchingDiffusion (ν : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  ∑ j, (vorticityField u x j • (ν • complexRealPartEuclideanCLM
    (spatialLaplacian (fun y ↦ coordinateDerivative (fullFourierField id u) j y) x)) +
      (ν • fullVorticityLaplacian u x) j • velocityJet u j x)

theorem stretchingMaterialRateField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (x : T3) :
    stretchingMaterialRateField ν u x = -pressureAction u x + stretchingDiffusion ν u x := by
  simp only [stretchingMaterialRateField, ContinuousMap.sum_apply, ContinuousMap.add_apply,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    gradientRemainderField_apply ν u hu hd hr, vorticityDiffusionField_apply ν u hu,
    velocityDerivativeField_apply, pressureAction, stretchingDiffusion,
    smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

/-- The signed material flux rate, with pressure and viscosity fully exposed. -/
theorem fluxMaterialRateField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (j : Fin 3) (x : T3) :
    fluxMaterialRateField ν u j x =
      -(stretchingField u x j • stretchingField u x) +
        vorticityField u x j • pressureAction u x -
        (ν • fullVorticityLaplacian u x) j • stretchingField u x -
        vorticityField u x j • stretchingDiffusion ν u x := by
  simp only [fluxMaterialRateField, pointwise, ContinuousMap.coe_mk,
    ContinuousLinearMap.lsmul_apply, componentField_apply,
    ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    stretchingMaterialRateField_apply ν u hu hd hr,
    vorticityDiffusionField_apply ν u hu, smul_add, smul_neg]
  abel

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxMaterialRate
