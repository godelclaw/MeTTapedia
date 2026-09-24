import Mettapedia.Analysis.WeightedMixedDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityVectorBernstein

/-!
# Actual mixed spatial jets and their weighted integration-by-parts bound

All jets are constructed from the same finite-support velocity. Commuting
the Fourier derivative multipliers identifies the common third derivative
in the two fluxes; it is not an independent cancellation hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityMixedJets

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths
open PancakeInfiniteFourierDerivative PancakeHigherDerivativeMoments PancakeDyadicDirectionEvolution
open PancakeInfiniteSpatialCurl PancakeTransverseEnergyFreezing PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeFilteredStrainDynamics LocalFilteredVorticity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open LocalWeightedCurlCancellation FourierFiniteSupport InfiniteFourierDiffusion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem derivative_eq_zero (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) (q : Wavevector) (hq : q ∉ P) :
    indexedDerivativeCoeff id j u q = 0 := by simp [indexedDerivativeCoeff, hs q hq]

theorem summable_norm (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : Summable (fun q ↦ ‖u q‖) :=
  summable_of_ne_finset_zero (s := P) (fun q hq ↦ by simp [hs q hq])

theorem continuous_mappedField (u : FourierVelocity) :
    Continuous (mappedField complexRealPartEuclideanCLM u) :=
  complexRealPartEuclideanCLM.continuous.comp (fullFourierField id u).continuous

theorem hasDerivAt_mappedField_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ mappedField complexRealPartEuclideanCLM u (x + coordinateShift j τ))
      (mappedField complexRealPartEuclideanCLM (indexedDerivativeCoeff id j u) (x + coordinateShift j t)) t :=
  complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_fullFourierField_shift id u (summable_norm P u hs) j
      (summable_norm P _ (derivative_eq_zero P u hs j)) t x)

def mixed (u : FourierVelocity) (j k : Fin 3) : T3 → R3 :=
  mappedField complexRealPartEuclideanCLM
    (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (fourierCurl u)))

def third (u : FourierVelocity) (j k : Fin 3) : T3 → R3 :=
  mappedField complexRealPartEuclideanCLM
    (indexedDerivativeCoeff id j (indexedDerivativeCoeff id k (indexedDerivativeCoeff id k (fourierCurl u))))

theorem mixed_diagonal (u : FourierVelocity) (j : Fin 3) : mixed u j j = fullCurlSecond u j := rfl

theorem mixed_commute (u : FourierVelocity) (j k : Fin 3) : mixed u j k = mixed u k j := by
  unfold mixed
  rw [indexedDerivativeCoeff_commute]

theorem hasDerivAt_gradient_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ fullCurlGradient u j (x + coordinateShift k τ))
      (mixed u j k (x + coordinateShift k t)) t :=
  hasDerivAt_mappedField_shift P _ (derivative_eq_zero P _ (fourierCurl_eq_zero P u hs) j) k x t

theorem hasDerivAt_second_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ fullCurlSecond u k (x + coordinateShift j τ))
      (third u j k (x + coordinateShift j t)) t :=
  hasDerivAt_mappedField_shift P _
    (derivative_eq_zero P _ (derivative_eq_zero P _ (fourierCurl_eq_zero P u hs) k) k) j x t

theorem hasDerivAt_mixed_shift (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ mixed u j k (x + coordinateShift k τ))
      (third u j k (x + coordinateShift k t)) t := by
  have he : indexedDerivativeCoeff id j (indexedDerivativeCoeff id k (indexedDerivativeCoeff id k (fourierCurl u))) =
      indexedDerivativeCoeff id k (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (fourierCurl u))) := by
    rw [indexedDerivativeCoeff_commute (indexedDerivativeCoeff id k (fourierCurl u)) j k,
      indexedDerivativeCoeff_commute (fourierCurl u) j k]
  unfold third
  rw [he]
  exact hasDerivAt_mappedField_shift P _
    (derivative_eq_zero P _ (derivative_eq_zero P _ (fourierCurl_eq_zero P u hs) j) k) k x t

theorem fourierCurl_derivative (u : FourierVelocity) (j : Fin 3) :
    fourierCurl (indexedDerivativeCoeff id j u) = indexedDerivativeCoeff id j (fourierCurl u) := by
  exact fourierCurl_filteredVelocity _ _

theorem fullVorticity_derivative (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) :
    fullVorticity (indexedDerivativeCoeff id j u) = fullCurlGradient u j := by
  unfold fullVorticity fullCurlGradient
  rw [spatialCurl_velocity _ (summable_fourierMoment P _ (derivative_eq_zero P u hs j) 1),
    fourierCurl_derivative]

theorem gradient_curl_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) (x : T3) :
    fullCurlGradient (fourierCurl u) j x = WeightedCurlCancellation.curlJet (fun k ↦ mixed u j k x) := by
  have h := fullVorticity_curl_eq_curlJet (indexedDerivativeCoeff id j u)
    (summable_fourierMoment P _ (derivative_eq_zero P u hs j) 2) x
  rw [fourierCurl_derivative, fullVorticity_derivative P _ (fourierCurl_eq_zero P u hs) j] at h
  simpa only [fullCurlGradient, fourierCurl_derivative, mixed, mappedField] using h

/-- The third derivative has cancelled from this bound on actual jets. -/
theorem integral_mixed_sq_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2) ≤
      (∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlSecond u j x‖ ^ 2) +
        7 * (∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlSecond u k x‖ ^ 2) +
        24 * (∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) +
        18 * (∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u k x‖ ^ 4) := by
  have hu3 := summable_fourierMoment P u hs 3
  exact WeightedMixedDerivative.integral_weighted_mixed_sq_le
    (fullVorticity u) (fullCurlGradient u j) (fullCurlGradient u k)
    (fullCurlSecond u j) (fullCurlSecond u k) (mixed u j k) (third u j k)
    (coordinateShift j) (coordinateShift k)
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (LocalPairedDiffusion.continuous_fullCurlSecond u j)
    (LocalPairedDiffusion.continuous_fullCurlSecond u k)
    (continuous_mappedField _) (continuous_mappedField _)
    (continuous_coordinateShift j) (continuous_coordinateShift k) (coordinateShift_zero j) (coordinateShift_zero k)
    (hasDerivAt_fullVorticity_shift u hu3 j) (hasDerivAt_fullVorticity_shift u hu3 k)
    (hasDerivAt_fullCurlGradient_shift u hu3 j) (hasDerivAt_gradient_shift P u hs j k)
    (hasDerivAt_second_shift P u hs j k) (hasDerivAt_mixed_shift P u hs j k)

end Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityMixedJets
