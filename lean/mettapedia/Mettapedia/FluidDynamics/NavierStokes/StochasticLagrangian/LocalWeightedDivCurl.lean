import Mettapedia.Analysis.UnitTorusContinuousRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicityAngularBudget

/-!
# Weighted div–curl identity for the actual periodic velocity

Incompressibility identifies the trace of the squared gradient with the
divergence of advection. A vorticity weight leaves an explicit signed flux;
the unweighted div–curl identity does not survive unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedDivCurl

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedCurlCancellation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeInfiniteSpatialPressure PancakePhysicalConvectionCoefficients
open PancakeLocalProjectedEquation
open PancakeLocalGradientEquation PancakeLocalStrainReality
open PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalSpatialVorticityJets CurlVorticitySource
open HelicityAngularSource HelicityAngularBudget SpatialAdvectionDivergence

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def advection (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (fullFourierField id (advectionCoeff u) x)

def advectionGradient (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM
    (fullFourierField id (indexedDerivativeCoeff id j (advectionCoeff u)) x)

def gradientSquare (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ m : Fin 3, ‖realComponentGradient u m x‖ ^ 2

theorem continuous_advection (u : FourierVelocity) : Continuous (advection u) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id (advectionCoeff u)).continuous

theorem continuous_advectionGradient (u : FourierVelocity) (j : Fin 3) :
    Continuous (advectionGradient u j) :=
  complexRealPartEuclideanCLM.continuous.comp
    (fullFourierField id (indexedDerivativeCoeff id j (advectionCoeff u))).continuous

theorem continuous_gradientSquare (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (gradientSquare u) :=
  continuous_finsetSum _ (fun m _ ↦ (continuous_realComponentGradient u hu m).norm.pow 2)

theorem hasDerivAt_advection_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ advection u (x + coordinateShift j t))
      (advectionGradient u j (x + coordinateShift j h)) h := by
  have ha : Summable (indexedFirstMoment id (advectionCoeff u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_advectionCoeff 1 u hu
  exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_fullFourierField_shift id _ (summable_norm_coefficients id _ ha) j
      (summable_norm_derivativeCoefficients id _ ha j) h x)

/-- Pointwise div–curl algebra, with the actual advection divergence. -/
theorem gradientSquare_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    gradientSquare u x = ‖fullVorticity u x‖ ^ 2 +
      ∑ j : Fin 3, advectionGradient u j x j := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have ha : Summable (indexedFirstMoment id (advectionCoeff u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_advectionCoeff 1 u hu
  have he : (fullFourierField id (advectionCoeff u) : T3 → VelocityCoefficient) =
      spatialAdvection (fullFourierField id u) := fullFourierField_advection u hu2 hd
  have hsum : (∑ j : Fin 3, advectionGradient u j x j) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        coordinateDerivative (fullFourierField id u) i x j *
          coordinateDerivative (fullFourierField id u) j x i).re := by
    rw [← divergence_advection u hu2 hd, ← he]
    simp only [spatialDivergence, coordinateDerivative_fullFourierField id _ ha,
      Complex.re_sum, advectionGradient, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, PiLp.toLp_apply]
  have hreal (i j : Fin 3) : (coordinateDerivative (fullFourierField id u) j x i).im = 0 := by
    have h := congrArg Complex.im (spatialVelocityGradient_reality u hu1 hr x i j)
    simp only [Complex.conj_im] at h
    change -(coordinateDerivative (fullFourierField id u) j x i).im =
      (coordinateDerivative (fullFourierField id u) j x i).im at h
    linarith
  rw [hsum]
  simp [gradientSquare, realComponentGradient, componentGradient, fullVorticity, spatialCurl,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Complex.mul_re, hreal]
  ring

theorem integral_weighted_divergence_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (n : ℕ) :
    (∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ n *
      ∑ j : Fin 3, advectionGradient u j x j) =
      -(∫ x : T3, ∑ j : Fin 3,
        weightRate n (fullVorticity u x) (fullCurlGradient u j x) * advection u x j) := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  have hW := (hw.norm.pow 2).pow n
  have hdW (j : Fin 3) : Continuous (fun x : T3 ↦
      weightRate n (fullVorticity u x) (fullCurlGradient u j x)) := by
    unfold weightRate
    exact (continuous_const.mul ((hw.norm.pow 2).pow (n - 1))).mul
      (continuous_const.mul (hw.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j)))
  have hv (j : Fin 3) : Continuous (fun x : T3 ↦ advection u x j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp (continuous_advection u)
  have hdv (j : Fin 3) : Continuous (fun x : T3 ↦ advectionGradient u j x j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp (continuous_advectionGradient u j)
  have hibp (j : Fin 3) :
      (∫ x : T3, weightRate n (fullVorticity u x) (fullCurlGradient u j x) * advection u x j) =
      -(∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ n * advectionGradient u j x j) := by
    apply UnitTorusContinuousRate.integral_rate_mul _ _ _ _ (coordinateShift j)
      hW (hv j) (hdW j) (hdv j) (continuous_coordinateShift j) (coordinateShift_zero j)
    · intro x h
      exact (hasDerivAt_fullVorticity_shift u hu j x h).norm_sq.fun_pow n
    · intro x h
      simpa [EuclideanSpace.inner_single_left] using
        (hasDerivAt_const h (EuclideanSpace.single j (1 : ℝ))).inner ℝ
          (hasDerivAt_advection_shift u hu j x h)
  simp_rw [Finset.mul_sum]
  have hi₁ (j : Fin 3) : Integrable (fun x : T3 ↦
      (‖fullVorticity u x‖ ^ 2) ^ n * advectionGradient u j x j) :=
    (hW.mul (hdv j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ (j : Fin 3) : Integrable (fun x : T3 ↦
      weightRate n (fullVorticity u x) (fullCurlGradient u j x) * advection u x j) :=
    ((hdW j).mul (hv j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ ↦ hi₁ j), integral_finsetSum _ (fun j _ ↦ hi₂ j)]
  simp only [hibp, Finset.sum_neg_distrib, neg_neg]

/-- The polynomially weighted div–curl identity retains its signed flux. -/
theorem integral_weighted_gradientSquare_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (n : ℕ) :
    (∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ n * gradientSquare u x) =
      (∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ (n + 1)) -
      ∫ x : T3, ∑ j : Fin 3,
        weightRate n (fullVorticity u x) (fullCurlGradient u j x) * advection u x j := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  have hA : Continuous (fun x : T3 ↦ ∑ j : Fin 3, advectionGradient u j x j) :=
    continuous_finsetSum _ (fun j _ ↦
      (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp (continuous_advectionGradient u j))
  simp_rw [gradientSquare_eq u hu hd hr, mul_add, ← pow_succ]
  have hi₁ : Integrable (fun x : T3 ↦ (‖fullVorticity u x‖ ^ 2) ^ (n + 1)) :=
    ((hw.norm.pow 2).pow (n + 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi₂ : Integrable (fun x : T3 ↦ (‖fullVorticity u x‖ ^ 2) ^ n *
      ∑ j : Fin 3, advectionGradient u j x j) :=
    (((hw.norm.pow 2).pow n).mul hA).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi₁ hi₂,
    integral_weighted_divergence_eq u hu n]
  rfl

theorem integral_gradientSquare_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, gradientSquare u x) = ∫ x : T3, ‖fullVorticity u x‖ ^ 2 := by
  simpa [weightRate] using integral_weighted_gradientSquare_eq u hu hd hr 0

theorem mixedGradientCost_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    mixedGradientCost u = (∫ x : T3, ‖fullVorticity u x‖ ^ 6) -
      4 * ∫ x : T3, ‖fullVorticity u x‖ ^ 2 *
        ∑ j : Fin 3, ⟪fullVorticity u x, fullCurlGradient u j x⟫ * advection u x j := by
  have h := integral_weighted_gradientSquare_eq u hu hd hr 2
  have he (x : T3) : (∑ j : Fin 3,
      weightRate 2 (fullVorticity u x) (fullCurlGradient u j x) * advection u x j) =
      4 * (‖fullVorticity u x‖ ^ 2 *
        ∑ j : Fin 3, ⟪fullVorticity u x, fullCurlGradient u j x⟫ * advection u x j) := by
    norm_num [weightRate, Fin.sum_univ_three]
    ring
  simpa only [mixedGradientCost, mixedGradientDensity, gradientSquare, ← pow_mul,
    he, integral_const_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedDivCurl
