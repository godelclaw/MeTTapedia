import Mettapedia.Analysis.UnitTorusProjectionFrameEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityProjectedBernstein

/-!
# Uniform vector-weighted bounds for finite vorticity jets

The fixed five-direction frame transfers actual scalar projection bounds
to vector norms. The constants precede the Fourier support, velocity, and
radius quantifiers. Coordinate second derivatives and the complete fourth
power of the first gradient are controlled; mixed second derivatives are
not asserted controlled by these statements alone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityVectorBernstein

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeHaarTransportRate PancakeFourierTranslationCurve
open FourierFiniteSupport LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open LocalWeightedCurlCancellation LocalVorticityEighthMoment GaussianRootWeightedIncrement
open FiniteVorticityProjectedBernstein

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_projected_first_fourth_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (e : R3) (j : Fin 3) :
    (∫ x : T3, ⟪e, fullVorticity u x⟫ ^ 4 * ⟪e, fullCurlGradient u j x⟫ ^ 4) ≤
      9 * (2 * Real.pi * R) ^ 2 *
        ∫ x : T3, ⟪e, fullVorticity u x⟫ ^ 6 * ⟪e, fullCurlGradient u j x⟫ ^ 2 := by
  have hu3 := summable_fourierMoment P u hs 3
  have h1 := UnitTorusQuarticSecondEnergy.integral_weightedFirst_fourth_le
    (fun x : T3 ↦ ⟪e, fullVorticity u x⟫) (fun x ↦ ⟪e, fullCurlGradient u j x⟫)
    (fun x ↦ ⟪e, fullCurlSecond u j x⟫) (coordinateShift j)
    (continuous_const.inner (continuous_fullVorticity u (summable_fourierMoment P u hs 1)))
    (continuous_const.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j))
    (continuous_const.inner (LocalPairedDiffusion.continuous_fullCurlSecond u j))
    (continuous_coordinateShift j) (coordinateShift_zero j)
    (fun x h ↦ by simpa only [inner_zero_left, zero_add, add_zero] using
      (hasDerivAt_const h e).inner ℝ (hasDerivAt_fullVorticity_shift u hu3 j x h))
    (fun x h ↦ by simpa only [inner_zero_left, zero_add, add_zero] using
      (hasDerivAt_const h e).inner ℝ (hasDerivAt_fullCurlGradient_shift u hu3 j x h))
  have h2 := integral_projected_second_sq_le P u hs R hP e j
  linarith only [h1, h2]

theorem exists_second_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → ∀ j : Fin 3,
      (∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlSecond u j x‖ ^ 2) ≤
        C * (2 * Real.pi * R) ^ 2 * ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlGradient u j x‖ ^ 2 := by
  obtain ⟨L, hL, htransfer⟩ := UnitTorusProjectionFrameEnergy.exists_transfer_constant
    (d := Fin 3) 3 1 3 1 (by norm_num) (by norm_num)
  refine ⟨L * 25, by positivity, fun P u hs R hP j ↦ ?_⟩
  have h := htransfer (fullVorticity u) (fullCurlGradient u j) (fullCurlSecond u j)
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalPairedDiffusion.continuous_fullCurlSecond u j) (25 * (2 * Real.pi * R) ^ 2)
    (by positivity) (fun k ↦ by
      simpa only [← pow_mul, Nat.reduceMul, pow_one] using
        integral_projected_second_sq_le P u hs R hP (QuadraticProjectionFrame.direction k) j)
  simpa only [Nat.reduceMul, mul_assoc] using h

theorem exists_first_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → ∀ j : Fin 3,
      (∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) ≤
        C * (2 * Real.pi * R) ^ 2 * ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlGradient u j x‖ ^ 2 := by
  obtain ⟨L, hL, htransfer⟩ := UnitTorusProjectionFrameEnergy.exists_transfer_constant
    (d := Fin 3) 2 2 3 1 (by norm_num) (by norm_num)
  refine ⟨L * 9, by positivity, fun P u hs R hP j ↦ ?_⟩
  have h := htransfer (fullVorticity u) (fullCurlGradient u j) (fullCurlGradient u j)
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j) (9 * (2 * Real.pi * R) ^ 2)
    (by positivity) (fun k ↦ by
      simpa only [← pow_mul, Nat.reduceMul, pow_one] using
        integral_projected_first_fourth_le P u hs R hP (QuadraticProjectionFrame.direction k) j)
  simpa only [Nat.reduceMul, mul_assoc] using h

theorem sum_integral_gradient_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    (∑ j : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlGradient u j x‖ ^ 2) =
      weightedPalinstrophy u := by
  have hω := continuous_fullVorticity u
    (PancakeHigherDerivativeMoments.summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu)
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * ‖fullCurlGradient u j x‖ ^ 2) :=
    ((hω.norm.pow 6).mul ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum _ (fun j _ ↦ hi j)]
  simp only [weightedPalinstrophy, weightedPalinstrophyDensity, Finset.mul_sum]

theorem gradient_square_le_three (v : Fin 3 → R3) :
    (∑ j : Fin 3, ‖v j‖ ^ 2) ^ 2 ≤ 3 * ∑ j : Fin 3, ‖v j‖ ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ ‖v j‖ ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at h
  have he : (∑ j : Fin 3, (‖v j‖ ^ 2) ^ 2) = ∑ j : Fin 3, ‖v j‖ ^ 4 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [he] at h

/-- The first term of the curvature cost has a uniform octic-dissipation
payer. This theorem does not cover the gradient of curl vorticity. -/
theorem exists_curl_gradient_product_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) →
      (∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
        (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2)) ≤
        C * (2 * Real.pi * R) ^ 2 * weightedPalinstrophy u := by
  obtain ⟨C, hC, hfirst⟩ := exists_first_constant
  refine ⟨6 * C, by positivity, fun P u hs R hP ↦ ?_⟩
  have hu2 := summable_fourierMoment P u hs 2
  have hω := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2)
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) :=
    ((hω.norm.pow 4).mul ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (x : T3) : ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
      (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) ≤
        6 * ∑ j : Fin 3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4 := by
    have hc := WeightedCurlCancellation.norm_curlJet_sq_le (fun j ↦ fullCurlGradient u j x)
    rw [← fullVorticity_curl_eq_curlJet u hu2 x] at hc
    have h1 := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ ‖fullVorticity u x‖ ^ 4 * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) by positivity)
    have h2 := mul_le_mul_of_nonneg_left (gradient_square_le_three (fun j ↦ fullCurlGradient u j x))
      (show 0 ≤ 2 * ‖fullVorticity u x‖ ^ 4 by positivity)
    rw [← Finset.mul_sum]
    nlinarith only [h1, h2]
  have hleft : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
      (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2)) :=
    (((hω.norm.pow 4).mul (hb.norm.pow 2)).mul (continuous_finsetSum _
      (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hleft ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul 6) hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hi j)] at h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    hfirst P u hs R hP j)
  rw [← Finset.mul_sum, sum_integral_gradient_eq u (summable_fourierMoment P u hs 3)] at hsum
  nlinarith only [h, hsum]

end Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityVectorBernstein
