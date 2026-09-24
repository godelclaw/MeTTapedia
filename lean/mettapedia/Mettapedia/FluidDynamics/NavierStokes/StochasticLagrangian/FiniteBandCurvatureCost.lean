import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityMixedJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionCurvatureBudget

/-!
# A universal finite-band bound for the full projection-curvature cost

The mixed-jet integration-by-parts estimate and the vector-weighted
Bernstein estimates pay both terms of the curvature cost with one copy
of the octic dissipation. The constant is chosen before the Fourier
support, field, and radius. The explicit radius squared is not removed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteBandCurvatureCost

open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeHaarTransportRate FourierFiniteSupport LocalLowDiffusionBudget
open LocalSpatialVorticityJets LocalJointDiffusionBudget LocalWeightedCurlCancellation
open LocalVorticityEighthMoment FiniteVorticityVectorBernstein FiniteVorticityMixedJets
open LocalProjectionCurvatureBudget

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mixedEnergy (u : FourierVelocity) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2

def curlGradientEnergy (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
    ∑ j : Fin 3, ‖fullCurlGradient (fourierCurl u) j x‖ ^ 2

theorem mixedEnergy_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    mixedEnergy u ≤
      24 * (∑ j : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ‖fullCurlSecond u j x‖ ^ 2) +
      126 * (∑ j : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    Finset.sum_le_sum (s := Finset.univ) (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) ↦
      integral_mixed_sq_le P u hs j k))
  simp only [mixedEnergy, Fin.sum_univ_three] at h ⊢
  linarith only [h]

theorem exists_mixed_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) →
      mixedEnergy u ≤ C * (2 * Real.pi * R) ^ 2 * weightedPalinstrophy u := by
  obtain ⟨C₂, hC₂, hsecond⟩ := exists_second_constant
  obtain ⟨C₁, hC₁, hfirst⟩ := exists_first_constant
  refine ⟨24 * C₂ + 126 * C₁, by positivity, fun P u hs R hP ↦ ?_⟩
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    hsecond P u hs R hP j)
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    hfirst P u hs R hP j)
  rw [← Finset.mul_sum, sum_integral_gradient_eq u (summable_fourierMoment P u hs 3)] at h1 h2
  nlinarith only [mixedEnergy_le P u hs, h1, h2]

theorem curlGradientEnergy_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : curlGradientEnergy u ≤ 2 * mixedEnergy u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hi (j k : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2) :=
    ((ha.norm.pow 6).mul ((continuous_mappedField _).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ∑ j : Fin 3, ‖fullCurlGradient (fourierCurl u) j x‖ ^ 2) :=
    ((ha.norm.pow 6).mul (continuous_finsetSum _ (fun j _ ↦
      (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u) j).norm.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hp (x : T3) : ‖fullVorticity u x‖ ^ 6 *
      (∑ j : Fin 3, ‖fullCurlGradient (fourierCurl u) j x‖ ^ 2) ≤
      2 * ∑ j : Fin 3, ∑ k : Fin 3, ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      WeightedCurlCancellation.norm_curlJet_sq_le (fun k ↦ mixed u j k x))
    simp_rw [← gradient_curl_eq P u hs] at h
    have hw := mul_le_mul_of_nonneg_left h (show 0 ≤ ‖fullVorticity u x‖ ^ 6 by positivity)
    simpa only [← Finset.mul_sum, mul_left_comm] using hw
  have h := integral_mono hleft
    ((integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hi j k))).const_mul 2) hp
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hi j k))] at h
  simp_rw [integral_finsetSum _ (fun k _ ↦ hi _ k)] at h
  exact h

theorem curvatureCost_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    curvatureCost u =
      70 * (∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
        (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2)) + 28 * curlGradientEnergy u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hb := continuous_fullVorticity (fourierCurl u)
    (summable_fourierMoment_curl 1 u (summable_fourierMoment P u hs 2))
  have hg (v : FourierVelocity) : Continuous (fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient v j x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient v j).norm.pow 2)
  have h1 : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
      (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2)) :=
    (((ha.norm.pow 4).mul (hb.norm.pow 2)).mul (hg u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ∑ j : Fin 3, ‖fullCurlGradient (fourierCurl u) j x‖ ^ 2) :=
    ((ha.norm.pow 6).mul (hg (fourierCurl u))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold curvatureCost curvatureCostDensity curlGradientEnergy
  simp only [mul_assoc]
  rw [integral_add (by simpa only [mul_assoc] using h1.const_mul 70)
    (by simpa only [mul_assoc] using h2.const_mul 28), integral_const_mul, integral_const_mul]

/-- No field-dependent constant, inverse regularization, or support
cardinality is hidden in this estimate. -/
theorem exists_curvature_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) →
      curvatureCost u ≤ C * (2 * Real.pi * R) ^ 2 * weightedPalinstrophy u := by
  obtain ⟨C₁, hC₁, hfirst⟩ := exists_curl_gradient_product_constant
  obtain ⟨C₂, hC₂, hmixed⟩ := exists_mixed_constant
  refine ⟨70 * C₁ + 56 * C₂, by positivity, fun P u hs R hP ↦ ?_⟩
  rw [curvatureCost_eq P u hs]
  nlinarith only [hfirst P u hs R hP, hmixed P u hs R hP, curlGradientEnergy_le P u hs]

end Mettapedia.FluidDynamics.NavierStokes.FiniteBandCurvatureCost
