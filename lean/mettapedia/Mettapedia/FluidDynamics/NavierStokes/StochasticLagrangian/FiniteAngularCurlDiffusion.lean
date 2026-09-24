import Mettapedia.Analysis.AngularCurlSecondVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAngularCurlEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityMixedJets

/-!
# Signed angular diffusion balance on actual finite Fourier fields

The vorticity, first jet and higher jets are reconstructed from the same
velocity coefficients. Periodic integration removes the ordinary density
Laplacian and leaves the full signed second variation. No curvature sign
or uniform time bound is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularCurlDiffusion

open MeasureTheory Mettapedia.Analysis AngularCurlDecomposition
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open LocalWeightedCurlCancellation LocalVorticityGradientEvolution LocalAngularCurlEvolution
open FiniteVorticityMixedJets FourierFiniteSupport InfiniteFourierDiffusion

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def firstRate (u : FourierVelocity) (k : Fin 3) (x : T3) : ℝ :=
  angularCurlDensityRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullCurlGradient u k x) (fun j ↦ mixed u j k x)

def curvature (u : FourierVelocity) (k : Fin 3) (x : T3) : ℝ :=
  angularCurlDensitySecondVariation (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullCurlGradient u k x) (fun j ↦ mixed u j k x)

def secondRate (u : FourierVelocity) (k : Fin 3) (x : T3) : ℝ :=
  curvature u k x + angularCurlDensityRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullCurlSecond u k x) (fun j ↦ third u j k x)

def curvatureDensity (u : FourierVelocity) (x : T3) : ℝ := ∑ k : Fin 3, curvature u k x

def densityLaplacian (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ k : Fin 3, deriv (deriv (fun h ↦ LocalAngularCurlBudget.angularCurlDensity u
    (x + coordinateShift k h))) 0

theorem hasDerivAt_density_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun h ↦ LocalAngularCurlBudget.angularCurlDensity u (x + coordinateShift k h))
      (firstRate u k (x + coordinateShift k t)) t :=
  hasDerivAt_angularCurlDensity
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment P u hs 3) k x t)
    (fun j ↦ hasDerivAt_gradient_shift P u hs j k x t)

theorem hasDerivAt_firstRate_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun h ↦ firstRate u k (x + coordinateShift k h))
      (secondRate u k (x + coordinateShift k t)) t :=
  hasDerivAt_angularCurlDensityRate
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment P u hs 3) k x t)
    (fun j ↦ hasDerivAt_gradient_shift P u hs j k x t)
    (hasDerivAt_fullCurlGradient_shift u (summable_fourierMoment P u hs 3) k x t)
    (fun j ↦ hasDerivAt_mixed_shift P u hs j k x t)

theorem densityLaplacian_eq_sum (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    densityLaplacian u x = ∑ k : Fin 3, secondRate u k x := by
  apply Finset.sum_congr rfl
  intro k _
  have hd : deriv (fun h ↦ LocalAngularCurlBudget.angularCurlDensity u (x + coordinateShift k h)) =
      fun h ↦ firstRate u k (x + coordinateShift k h) :=
    funext (fun h ↦ (hasDerivAt_density_shift P u hs k x h).deriv)
  rw [hd]
  simpa only [coordinateShift_zero, add_zero] using (hasDerivAt_firstRate_shift P u hs k x 0).deriv

theorem sum_third_eq_gradientLaplacian (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) (x : T3) :
    (∑ k : Fin 3, third u j k x) = gradientLaplacian u j x := by
  have hc := summable_fourierMoment P _ (derivative_eq_zero P _ (fourierCurl_eq_zero P u hs) j) 2
  simp only [gradientLaplacian, spatialLaplacian, coordinateDerivative2_fullFourierField _ hc, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold third mappedField
  rw [indexedDerivativeCoeff_commute (indexedDerivativeCoeff id k (fourierCurl u)) j k,
    indexedDerivativeCoeff_commute (fourierCurl u) j k]

theorem viscousDensityRate_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    viscousDensityRate u x = densityLaplacian u x - curvatureDensity u x := by
  rw [densityLaplacian_eq_sum P u hs]
  unfold viscousDensityRate
  rw [← sum_fullCurlSecond u (summable_fourierMoment P u hs 3) x]
  have hg : (fun j ↦ gradientLaplacian u j x) = fun j ↦ ∑ k : Fin 3, third u j k x :=
    funext (fun j ↦ (sum_third_eq_gradientLaplacian P u hs j x).symm)
  rw [hg]
  simp only [secondRate, curvatureDensity, Fin.sum_univ_three, angularCurlDensityRate_add]
  ring

theorem continuous_firstRate (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (k : Fin 3) : Continuous (firstRate u k) :=
  continuous_angularCurlDensityRate _ _ _ _
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u) (fun _ ↦ continuous_mappedField _)

theorem continuous_curvature (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (k : Fin 3) : Continuous (curvature u k) :=
  continuous_angularCurlDensitySecondVariation _ _ _ _
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u) (fun _ ↦ continuous_mappedField _)

theorem continuous_secondRate (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (k : Fin 3) : Continuous (secondRate u k) :=
  (continuous_curvature P u hs k).add (continuous_angularCurlDensityRate _ _ _ _
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalPairedDiffusion.continuous_fullCurlSecond u k)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u) (fun _ ↦ continuous_mappedField _))

theorem integral_densityLaplacian_eq_zero (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : (∫ x : T3, densityLaplacian u x) = 0 := by
  have hi (k : Fin 3) : Integrable (secondRate u k) :=
    (continuous_secondRate P u hs k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz (k : Fin 3) : (∫ x : T3, secondRate u k x) = 0 :=
    UnitTorusContinuousRate.integral_rate_eq_zero (firstRate u k) (secondRate u k) (coordinateShift k)
      (continuous_firstRate P u hs k) (continuous_secondRate P u hs k)
      (continuous_coordinateShift k) (coordinateShift_zero k) (hasDerivAt_firstRate_shift P u hs k)
  simp_rw [densityLaplacian_eq_sum P u hs]
  rw [integral_finsetSum _ (fun k _ ↦ hi k)]
  simp only [hz, Finset.sum_const_zero]

theorem integral_viscousDensityRate_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, viscousDensityRate u x) = -(∫ x : T3, curvatureDensity u x) := by
  have hiL : Integrable (densityLaplacian u) := by
    have he : densityLaplacian u = fun x ↦ ∑ k : Fin 3, secondRate u k x :=
      funext (densityLaplacian_eq_sum P u hs)
    rw [he]
    exact (continuous_finsetSum _ (fun k _ ↦ continuous_secondRate P u hs k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (curvatureDensity u) :=
    (continuous_finsetSum _ (fun k _ ↦ continuous_curvature P u hs k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [viscousDensityRate_eq P u hs]
  rw [integral_sub hiL hiC, integral_densityLaplacian_eq_zero P u hs, zero_sub]

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularCurlDiffusion
