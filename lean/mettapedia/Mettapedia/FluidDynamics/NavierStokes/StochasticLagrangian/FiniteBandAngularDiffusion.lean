import Mettapedia.Analysis.AngularCurlCurvatureBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularCurlDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandCurvatureCost

/-!
# Finite-band payment of angular corrected-energy diffusion

The universal curvature bound charges weighted first- and second-jet
energies once. Existing vector-weighted Bernstein and mixed-jet estimates
bound these by radius squared times octic dissipation. A sufficiently
large normalization absorbs the viscous correction. This does not bound
the nonlinear spectral mismatch or subgrid work at that normalization.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteBandAngularDiffusion

open MeasureTheory Mettapedia.Analysis AngularCurlDecomposition
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FiniteVorticityMixedJets FourierFiniteSupport FiniteVorticityVectorBernstein
open FiniteAngularCurlDiffusion LocalAngularCurlEvolution LocalProjectionCurvatureBudget

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem curvatureDensity_le (u : FourierVelocity) (x : T3) :
    curvatureDensity u x ≤
      6048 * ∑ j : Fin 3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4 +
        672 * ∑ j : Fin 3, ∑ k : Fin 3, ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) ↦
    angularCurlDensitySecondVariation_le (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
      (fullCurlGradient u k x) (fun j ↦ mixed u j k x))
  have hg := mul_le_mul_of_nonneg_left (gradient_square_le_three (fun j ↦ fullCurlGradient u j x))
    (show 0 ≤ 2016 * ‖fullVorticity u x‖ ^ 4 by positivity)
  simp only [curvatureDensity, curvature, Fin.sum_univ_three] at h ⊢
  simp only [Fin.sum_univ_three] at hg
  nlinarith only [h, hg]

theorem integral_curvatureDensity_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, curvatureDensity u x) ≤
      6048 * (∑ j : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) +
        672 * FiniteBandCurvatureCost.mixedEnergy u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have h₁ (j : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 * ‖fullCurlGradient u j x‖ ^ 4) :=
    ((ha.norm.pow 4).mul ((LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₂ (j k : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * ‖mixed u j k x‖ ^ 2) :=
    ((ha.norm.pow 6).mul ((continuous_mappedField _).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (curvatureDensity u) :=
    (continuous_finsetSum _ (fun k _ ↦ continuous_curvature P u hs k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hc
    (((integrable_finsetSum _ (fun j _ ↦ h₁ j)).const_mul 6048).add
      ((integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ h₂ j k))).const_mul 672))
    (curvatureDensity_le u)
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_finsetSum Finset.univ (fun j _ ↦ h₁ j)).const_mul 6048)
    ((integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ h₂ j k))).const_mul 672)] at h
  simp only [integral_const_mul] at h
  rw [integral_finsetSum _ (fun j _ ↦ h₁ j),
    integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ h₂ j k))] at h
  simp_rw [integral_finsetSum _ (fun k _ ↦ h₂ _ k)] at h
  exact h

/-- The constant precedes the support, velocity and radius quantifiers. -/
theorem exists_curvature_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) →
      (∫ x : T3, curvatureDensity u x) ≤ C * (2 * Real.pi * R) ^ 2 * weightedPalinstrophy u := by
  obtain ⟨C₁, hC₁, hfirst⟩ := exists_first_constant
  obtain ⟨C₂, hC₂, hmixed⟩ := FiniteBandCurvatureCost.exists_mixed_constant
  refine ⟨6048 * C₁ + 672 * C₂, by positivity, fun P u hs R hP ↦ ?_⟩
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    hfirst P u hs R hP j)
  rw [← Finset.mul_sum, sum_integral_gradient_eq u (summable_fourierMoment P u hs 3)] at h₁
  nlinarith only [integral_curvatureDensity_le P u hs, h₁, hmixed P u hs R hP]

def correctedViscousDensity (ν κ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ν * octicViscousDensity u x - (3 * ν / κ) * viscousDensityRate u x

theorem integral_correctedViscousDensity_eq (ν κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, correctedViscousDensity ν κ u x) =
      -ν * weightedPalinstrophy u - 6 * ν * radialDissipation u +
        (3 * ν / κ) * (∫ x : T3, curvatureDensity u x) := by
  have hu3 := summable_fourierMoment P u hs 3
  have hi : Integrable (viscousDensityRate u) := by
    have he : viscousDensityRate u = fun x ↦ (∑ k : Fin 3, secondRate u k x) - curvatureDensity u x := by
      funext x
      rw [viscousDensityRate_eq P u hs, densityLaplacian_eq_sum P u hs]
    rw [he]
    exact ((continuous_finsetSum _ (fun k _ ↦ continuous_secondRate P u hs k)).sub
      (continuous_finsetSum _ (fun k _ ↦ continuous_curvature P u hs k))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold correctedViscousDensity
  rw [integral_sub ((integrable_octicViscousDensity u hu3).const_mul ν) (hi.const_mul (3 * ν / κ))]
  simp only [integral_const_mul, integral_octicViscousDensity u hu3, integral_viscousDensityRate_eq P u hs]
  ring

/-- Viscous absorption is compatible with a normalization proportional
to radius squared. No claim about nonlinear work is included. -/
theorem exists_diffusion_threshold :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Wavevector) (u : FourierVelocity),
      (∀ q, q ∉ P → u q = 0) → ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) →
      ∀ ν κ : ℝ, 0 ≤ ν → 0 < κ → 6 * C * (2 * Real.pi * R) ^ 2 ≤ κ →
      (∫ x : T3, correctedViscousDensity ν κ u x) ≤
        -(ν / 2) * weightedPalinstrophy u - 6 * ν * radialDissipation u := by
  obtain ⟨C, hC, hbound⟩ := exists_curvature_constant
  refine ⟨C, hC, fun P u hs R hP ν κ hν hκ hscale ↦ ?_⟩
  rw [integral_correctedViscousDensity_eq ν κ P u hs]
  have hb := mul_le_mul_of_nonneg_left (hbound P u hs R hP)
    (show 0 ≤ 3 * ν / κ by positivity)
  have hp := mul_le_mul_of_nonneg_right hscale
    (mul_nonneg hν (weightedPalinstrophy_nonneg u))
  apply (le_of_mul_le_mul_right (a := κ) ?_ hκ)
  have hbκ := mul_le_mul_of_nonneg_right hb hκ.le
  field_simp at hbκ ⊢
  nlinarith only [hp, hbκ]

end Mettapedia.FluidDynamics.NavierStokes.FiniteBandAngularDiffusion
