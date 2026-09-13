import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MovingProjectionBudget

/-!
# Removing fixed-band normalization speed by a bounded integrating factor

An increasing scalar normalization contributes an affordable coefficient
when the Fourier multiplier stays fixed. The integrating factor lies
between one and `exp 1` whenever the initial band is admitted. The actual
signed nonlinear remainder is retained; no estimate for it is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MovingProjectionIntegratingFactor

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open FiniteBandProjectionAbsorption LocalProjectionScaleMotion MovingProjectionBudget
open LocalVorticityEighthMoment FilteredProjectionMean

def factor (R₀ R : ℝ) : ℝ := Real.exp (48 * (8 * Real.pi * R₀) ^ 2 / normalization R)

theorem factor_bounds (R₀ R : ℝ)
    (hscale : 48 * (8 * Real.pi * R₀) ^ 2 ≤ normalization R) :
    1 ≤ factor R₀ R ∧ factor R₀ R ≤ Real.exp 1 := by
  constructor
  · exact Real.one_le_exp (by unfold normalization; have hc := curvatureConstant_pos; positivity)
  · exact Real.exp_le_exp.mpr ((div_le_one (normalization_pos R)).mpr hscale)

theorem hasDerivAt_factor (R₀ : ℝ) {R : ℝ → ℝ} {dR t : ℝ}
    (hR : HasDerivAt R dR t) :
    HasDerivAt (fun τ ↦ factor R₀ (R τ))
      (-(48 * (8 * Real.pi * R₀) ^ 2 *
        (normalizationRate (R t) * dR / normalization (R t) ^ 2)) * factor R₀ (R t)) t := by
  have hκ := (hasDerivAt_normalization (R t)).comp t hR
  have hi := (hκ.inv (normalization_pos (R t)).ne').const_mul (48 * (8 * Real.pi * R₀) ^ 2)
  have he := hi.exp
  simp only [Pi.inv_def, div_eq_mul_inv] at he
  change HasDerivAt (fun τ ↦ factor R₀ (R τ)) _ t at he
  apply he.congr_deriv
  unfold factor
  simp only [Function.comp_apply]
  ring

theorem differentiableAt_correctedEnergy {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ (fun τ ↦ correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t := by
  have h := (MovingProjectionMean.hasDerivAt_mean s hν hB
    (fun τ ↦ normalization (R τ)) (fun τ ↦ normalizationRate (R τ) * dR τ)
    (continuous_normalization.comp_continuousOn hR)
    ((continuous_normalizationRate.comp_continuousOn hR).mul hdR)
    (fun τ _ ↦ normalization_pos (R τ))
    (fun τ hτ ↦ (hasDerivAt_normalization (R τ)).comp τ (hder τ hτ)) P χ hcut t ht).differentiableAt
  change DifferentiableAt ℝ (fun τ ↦ meanCorrectedEnergy (regularization ν (R τ))
    (normalization (R τ)) (filteredVelocity χ (s.coefficients τ))) t at h
  simpa only [FilteredProjectionAbsorption.meanCorrectedEnergy_eq ν _ hν P χ hcut] using h

/-- The actual NS inequality after absorbing the scalar motion. The
right-hand side still contains the full signed nonlinear remainder. -/
theorem deriv_weighted_correctedEnergy_add_dissipation_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R t)
    (R₀ : ℝ) (hP₀ : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R₀)
    (hRn : 0 ≤ R t) (hdn : 0 ≤ dR t) :
    deriv (fun τ ↦ factor R₀ (R τ) *
      correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t +
      factor R₀ (R t) * ((ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
        3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t))) ≤
      factor R₀ (R t) *
        FilteredCoherentProjectionBudget.signedWorkRemainder ν (R t) P χ (s.coefficients t) := by
  have he := differentiableAt_correctedEnergy s hν hB R dR hR hdR hder P χ hcut t ht
  have hf := hasDerivAt_factor R₀ (hder t ht)
  rw [(hf.fun_mul he.hasDerivAt).deriv]
  have h := deriv_correctedEnergy_add_dissipation_le_fixed_band
    s hν hB R dR hR hdR hder P χ hcut C hχ t ht hP R₀ hP₀
  rw [abs_of_nonneg (mul_nonneg (normalizationRate_nonneg (R t) hRn) hdn)] at h
  have hp : 0 ≤ factor R₀ (R t) := (Real.exp_pos _).le
  nlinarith only [mul_le_mul_of_nonneg_left h hp]

end Mettapedia.FluidDynamics.NavierStokes.MovingProjectionIntegratingFactor
