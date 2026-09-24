import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MovingProjectionMean
import Mettapedia.Analysis.LogarithmicScaleCost
import Mettapedia.Analysis.ReciprocalScaleCost

/-!
# Coherent energy inequality with an adaptive scalar normalization

The actual fixed-multiplier NS inequality survives a differentiable
change of normalization, with one explicit signed scale-motion term.
The coarse alternative charges logarithmic normalization speed. Retaining
a fixed support radius instead gives inverse-square speed, whose time
integral is bounded for an increasing normalization. No bound for the
remaining nonlinear work, or for a moving multiplier, is inferred.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MovingProjectionBudget

open MeasureTheory PeriodicFourierTriad PancakeGalerkinKineticEnergy
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation LocalVorticityEighthMoment
open FiniteVorticityVariation FilteredProjectionMean FiniteBandProjectionAbsorption
open LocalProjectionScaleMotion MovingProjectionMean
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem deriv_mean_eq_fixed_add_scale {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (κ dκ : ℝ → ℝ) (hk : ContinuousOn κ (Set.Icc (0 : ℝ) T))
    (hdk : ContinuousOn dκ (Set.Icc (0 : ℝ) T))
    (hκ : ∀ τ ∈ Set.Icc (0 : ℝ) T, 0 < κ τ)
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt κ (dκ τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ meanCorrectedEnergy (ν ^ 2 * κ τ ^ 2 / 3) (κ τ)
      (filteredVelocity χ (s.coefficients τ))) t =
      deriv (fun τ ↦ meanCorrectedEnergy (ν ^ 2 * κ t ^ 2 / 3) (κ t)
        (filteredVelocity χ (s.coefficients τ))) t +
          scaleWork ν (κ t) (dκ t) (filteredVelocity χ (s.coefficients t)) := by
  have hp := hκ t (Set.Ioo_subset_Icc_self ht)
  have hδ : 0 < ν ^ 2 * κ t ^ 2 / 3 := by positivity
  have hd := (hasDerivAt_mean s hν hB κ dκ hk hdk hκ hder P χ hcut t ht).deriv
  have hf := (hasDerivAt_meanCorrectedEnergy s hB _ hδ (κ t) P χ hcut t ht).deriv
  rw [hd, hf]
  exact integral_movingRate_eq ν (κ t) (dκ t) hν hp P _ _
    (fun q hq ↦ by simp [filteredVelocity, hcut q hq])
    (fun q hq ↦ by simp [filteredVelocity, hcut q hq])

theorem continuous_normalization : Continuous normalization :=
  continuous_iff_continuousAt.mpr fun R ↦ (hasDerivAt_normalization R).continuousAt

theorem continuous_normalizationRate : Continuous normalizationRate := by
  unfold normalizationRate
  fun_prop

theorem deriv_correctedEnergy_eq_fixed_add_scale {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t =
      deriv (fun τ ↦ correctedEnergy ν (R t) (filteredVelocity χ (s.coefficients τ))) t +
        scaleWork ν (normalization (R t)) (normalizationRate (R t) * dR t)
          (filteredVelocity χ (s.coefficients t)) := by
  have hk := continuous_normalization.comp_continuousOn hR
  have hdk := (continuous_normalizationRate.comp_continuousOn hR).mul hdR
  have he := deriv_mean_eq_fixed_add_scale s hν hB
    (fun τ ↦ normalization (R τ)) (fun τ ↦ normalizationRate (R τ) * dR τ)
    hk hdk (fun τ _ ↦ normalization_pos (R τ))
    (fun τ hτ ↦ (hasDerivAt_normalization (R τ)).comp τ (hder τ hτ)) P χ hcut t ht
  change deriv (fun τ ↦ meanCorrectedEnergy (regularization ν (R τ)) (normalization (R τ))
    (filteredVelocity χ (s.coefficients τ))) t =
      deriv (fun τ ↦ meanCorrectedEnergy (regularization ν (R t)) (normalization (R t))
        (filteredVelocity χ (s.coefficients τ))) t + _ at he
  simpa only [FilteredProjectionAbsorption.meanCorrectedEnergy_eq ν _ hν P χ hcut] using he

/-- The multiplier is fixed, so its own derivative contributes no term.
Only the scalar normalization moves. -/
theorem deriv_correctedEnergy_add_dissipation_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R t) :
    deriv (fun τ ↦ correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t +
      (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
      3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      FilteredCoherentProjectionBudget.signedWorkRemainder ν (R t) P χ (s.coefficients t) +
        scaleWork ν (normalization (R t)) (normalizationRate (R t) * dR t)
          (filteredVelocity χ (s.coefficients t)) := by
  rw [deriv_correctedEnergy_eq_fixed_add_scale s hν hB R dR hR hdR hder P χ hcut t ht]
  have h := FilteredCoherentProjectionBudget.deriv_correctedEnergy_add_dissipation_le
    s hν hB (R t) P hP χ hcut C hχ t ht
  linarith only [h]

theorem deriv_correctedEnergy_add_dissipation_le_logarithmic_rate {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R t) :
    deriv (fun τ ↦ correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t +
      (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
      3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      FilteredCoherentProjectionBudget.signedWorkRemainder ν (R t) P χ (s.coefficients t) +
        (|normalizationRate (R t) * dR t| / normalization (R t)) *
          correctedEnergy ν (R t) (filteredVelocity χ (s.coefficients t)) := by
  have h := deriv_correctedEnergy_add_dissipation_le s hν hB R dR hR hdR hder P χ hcut C hχ t ht hP
  have hcost := abs_scaleWork_le_logarithmic_rate ν (R t) (normalizationRate (R t) * dR t)
    hν P (filteredVelocity χ (s.coefficients t))
    (fun q hq ↦ by simp [filteredVelocity, hcut q hq]) hP
  exact h.trans (add_le_add le_rfl ((le_abs_self _).trans hcost))

/-- Keeping the actual support radius separate from the changing
normalization yields the sharper inverse-square-speed coefficient. -/
theorem deriv_correctedEnergy_add_dissipation_le_fixed_band {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R dR : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) T))
    (hdR : ContinuousOn dR (Set.Icc (0 : ℝ) T))
    (hder : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt R (dR τ) τ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R t)
    (R₀ : ℝ) (hP₀ : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R₀) :
    deriv (fun τ ↦ correctedEnergy ν (R τ) (filteredVelocity χ (s.coefficients τ))) t +
      (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
      3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      FilteredCoherentProjectionBudget.signedWorkRemainder ν (R t) P χ (s.coefficients t) +
        (48 * (8 * Real.pi * R₀) ^ 2 *
          (|normalizationRate (R t) * dR t| / normalization (R t) ^ 2)) *
          correctedEnergy ν (R t) (filteredVelocity χ (s.coefficients t)) := by
  have h := deriv_correctedEnergy_add_dissipation_le s hν hB R dR hR hdR hder P χ hcut C hχ t ht hP
  have hcost := abs_scaleWork_le_fixed_band ν (R t) R₀ (normalizationRate (R t) * dR t)
    hν P (filteredVelocity χ (s.coefficients t))
    (fun q hq ↦ by simp [filteredVelocity, hcut q hq]) hP₀ hP
  exact h.trans (add_le_add le_rfl ((le_abs_self _).trans hcost))

theorem normalizationRate_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ normalizationRate R := by
  have hc := curvatureConstant_pos
  unfold normalizationRate
  positivity

/-- The stronger fixed-band coefficient has finite mass controlled by its
initial normalization. This is not a bound on nonlinear stretching. -/
theorem integral_fixed_band_scale_coefficient_le (R dR : ℝ → ℝ) (R₀ a b : ℝ)
    (hab : a ≤ b) (hR : ContinuousOn R (Set.Icc a b))
    (hdR : ContinuousOn dR (Set.Icc a b))
    (hder : ∀ t ∈ Set.Ioo a b, HasDerivAt R (dR t) t)
    (hRn : ∀ t ∈ Set.Icc a b, 0 ≤ R t) (hdn : ∀ t ∈ Set.Icc a b, 0 ≤ dR t) :
    (∫ t in a..b, 48 * (8 * Real.pi * R₀) ^ 2 *
      (|normalizationRate (R t) * dR t| / normalization (R t) ^ 2)) ≤
      48 * (8 * Real.pi * R₀) ^ 2 / normalization (R a) := by
  have h := Mettapedia.Analysis.ReciprocalScaleCost.integral_abs_rate_div_sq_le_inv_of_nonneg
    (fun t ↦ normalization (R t)) (fun t ↦ normalizationRate (R t) * dR t) a b hab
    (continuous_normalization.comp_continuousOn hR)
    ((continuous_normalizationRate.comp_continuousOn hR).mul hdR)
    (fun t _ ↦ normalization_pos (R t))
    (fun t ht ↦ (hasDerivAt_normalization (R t)).comp t (hder t ht))
    (fun t ht ↦ mul_nonneg (normalizationRate_nonneg (R t) (hRn t ht)) (hdn t ht))
  rw [intervalIntegral.integral_const_mul]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h
    (show 0 ≤ 48 * (8 * Real.pi * R₀) ^ 2 by positivity)

/-- Starting the normalization at the fixed band's radius makes the
coefficient mass at most one, uniformly in that initial radius. -/
theorem integral_initial_band_scale_coefficient_le_one (R dR : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hR : ContinuousOn R (Set.Icc a b))
    (hdR : ContinuousOn dR (Set.Icc a b))
    (hder : ∀ t ∈ Set.Ioo a b, HasDerivAt R (dR t) t)
    (hRn : ∀ t ∈ Set.Icc a b, 0 ≤ R t) (hdn : ∀ t ∈ Set.Icc a b, 0 ≤ dR t) :
    (∫ t in a..b, 48 * (8 * Real.pi * R a) ^ 2 *
      (|normalizationRate (R t) * dR t| / normalization (R t) ^ 2)) ≤ 1 := by
  have h := integral_fixed_band_scale_coefficient_le R dR (R a) a b hab hR hdR hder hRn hdn
  exact h.trans ((div_le_one (normalization_pos (R a))).mpr (coercivity_scale_le (R a)))

/-- The coarse coefficient need not have a uniform bound when the
normalization diverges. It must not be confused with the fixed-band one. -/
theorem log_normalization_sub_le_integral_relative_speed (R dR : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hR : ContinuousOn R (Set.Icc a b))
    (hdR : ContinuousOn dR (Set.Icc a b))
    (hder : ∀ t ∈ Set.Ioo a b, HasDerivAt R (dR t) t) :
    Real.log (normalization (R b)) - Real.log (normalization (R a)) ≤
      ∫ t in a..b, |normalizationRate (R t) * dR t| / normalization (R t) :=
  Mettapedia.Analysis.LogarithmicScaleCost.log_sub_le_integral_abs_rate
    (fun t ↦ normalization (R t)) (fun t ↦ normalizationRate (R t) * dR t) a b hab
    (continuous_normalization.comp_continuousOn hR)
    ((continuous_normalizationRate.comp_continuousOn hR).mul hdR)
    (fun t _ ↦ normalization_pos (R t))
    (fun t ht ↦ (hasDerivAt_normalization (R t)).comp t (hder t ht))

end Mettapedia.FluidDynamics.NavierStokes.MovingProjectionBudget
