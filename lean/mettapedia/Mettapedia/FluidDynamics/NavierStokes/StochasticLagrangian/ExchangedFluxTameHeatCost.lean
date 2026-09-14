import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxTameAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxSectorHeatCost

/-!
# Combining multiplicative and additive heat-test estimates

The pointwise minimum retains both valid envelopes. The selected-sector
gain is preserved. The envelopes remain regularity-dependent, and their
time integrals need not be finite or bounded by initial data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxTameHeatCost

open MeasureTheory
open scoped ENNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail FourierHeatFlow LongitudinalGradientFlux
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open InfiniteConvectionEnergy PancakeLatticeDecayEnvelope
open ExchangedFluxAdjointSectors ExchangedFluxTameAdjoint ExchangedFluxHeatAdjoint
open ExchangedFluxHeatDualBudget ExchangedFluxHeatTestEstimate ExchangedFluxSectorHeatCost

local notation "C3" => EuclideanSpace ℂ (Fin 3)

def tameHeatEnvelope (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  tameEnvelope (54 * (2 * Real.pi)) (coefficients ν σ u) (projectedFlux 0 (coefficients ν σ u))

def minHeatEnvelope (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  min (heatTestEnvelope ν σ u) (tameHeatEnvelope ν σ u)

def weightedCost (A : ℝ → ℝ → Wavevector → C3) (t : ℝ) : ℝ≥0∞ :=
  ∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2) *
    (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t, ENNReal.ofReal (‖A σ τ q‖ ^ 2))

theorem weightedCost_le_of_tsum_le (A : ℝ → ℝ → Wavevector → C3) (t : ℝ)
    (B : ℝ → ℝ → ℝ≥0∞)
    (hB : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      (∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖A σ τ q‖ ^ 2)) ≤ B σ τ) :
    weightedCost A t ≤ ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t, B σ τ := by
  let f := fun q σ τ ↦ ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖A σ τ q‖ ^ 2)
  have he : weightedCost A t =
      ∑' q, ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ := by
    apply tsum_congr
    intro q
    simp only [f, ENNReal.ofReal_mul (sq_nonneg _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [he]
  apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
    (volume.restrict (Set.Ioi 0)) (fun q σ ↦ ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ)).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
    (volume.restrict (Set.Ioc 0 t)) (fun q τ ↦ f q σ τ)).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  exact hB σ hσ τ hτ

theorem tsum_weighted_heatTest_sq_le_tame {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, (1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ u q‖ ^ 2) ≤ tameHeatEnvelope ν σ u := by
  have h := ExchangedFluxTameAdjoint.tsum_weighted_coefficientTest_sq_le (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, heatCoefficientTest, tameHeatEnvelope] using h

theorem tsum_ofReal_weighted_heatTest_sq_le_min {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ u q‖ ^ 2)) ≤
      ENNReal.ofReal (minHeatEnvelope ν σ u) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (summable_weighted_heatTest_sq hν hσ u hu hF)]
  exact ENNReal.ofReal_le_ofReal (le_min (tsum_weighted_heatTest_sq_le hν hσ u hu hF)
    (tsum_weighted_heatTest_sq_le_tame hν hσ u hu hF))

theorem positiveTestCost_le_minEnvelope {ν : ℝ} (hν : 0 ≤ ν)
    (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (u τ) n ^ 2)) :
    positiveTestCost ν u t ≤ ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (minHeatEnvelope ν σ (u τ)) :=
  weightedCost_le_of_tsum_le (fun σ τ q ↦ heatCoefficientTest ν σ (u τ) q) t _
    (fun σ hσ τ hτ ↦ tsum_ofReal_weighted_heatTest_sq_le_min hν hσ.le (u τ) (hu τ hτ) (hF σ hσ τ hτ))

theorem tsum_weighted_selectedHeatTest_sq_le_tame {δ η ν σ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, (1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ u q‖ ^ 2) ≤
      sectorFactor δ η ^ 2 * tameHeatEnvelope ν σ u := by
  have h := ExchangedFluxTameAdjoint.tsum_weighted_selectedTest_sq_le hδ hη (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, selectedHeatTest, tameHeatEnvelope] using h

theorem tsum_ofReal_weighted_selectedHeatTest_sq_le_min {δ η ν σ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ u q‖ ^ 2)) ≤
      ENNReal.ofReal (sectorFactor δ η ^ 2) * ENNReal.ofReal (minHeatEnvelope ν σ u) := by
  by_cases h : heatTestEnvelope ν σ u ≤ tameHeatEnvelope ν σ u
  · simpa only [minHeatEnvelope, min_eq_left h] using
      tsum_ofReal_weighted_selectedHeatTest_sq_le hδ hη hν hσ u hu hF
  · rw [minHeatEnvelope, min_eq_right (le_of_not_ge h), ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (summable_weighted_selectedHeatTest_sq hδ hη hν hσ u hu hF)]
    exact ENNReal.ofReal_le_ofReal (tsum_weighted_selectedHeatTest_sq_le_tame hδ hη hν hσ u hu hF)

theorem selectedHeatCost_le_minEnvelope {δ η ν : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (u τ) n ^ 2)) :
    selectedHeatCost δ η ν u t ≤ ENNReal.ofReal (sectorFactor δ η ^ 2) *
      (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (minHeatEnvelope ν σ (u τ))) := by
  have h := weightedCost_le_of_tsum_le (fun σ τ q ↦ selectedHeatTest δ η ν σ (u τ) q) t
    (fun σ τ ↦ ENNReal.ofReal (sectorFactor δ η ^ 2) * ENNReal.ofReal (minHeatEnvelope ν σ (u τ)))
    (fun σ hσ τ hτ ↦ tsum_ofReal_weighted_selectedHeatTest_sq_le_min
      hδ hη hν hσ.le (u τ) (hu τ hτ) (hF σ hσ τ hτ))
  simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, weightedCost, selectedHeatCost] using h

theorem absolutePairingCost_le_initial_add_minEnvelope {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (g : Wavevector → ℝ)
    (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (hν : 0 < ν) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (s.coefficients τ) n ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal ε * ENNReal.ofReal
        ((2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) * ∑' q, latticeDecayWeight q) +
      ENNReal.ofReal ε⁻¹ * (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (minHeatEnvelope ν σ (s.coefficients τ))) := by
  have hu2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hU : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (s.coefficients τ)) :=
    fun τ hτ ↦ hsg.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu τ ⟨hτ.1.le, hτ.2.trans ht.2⟩)
  exact (absolutePairingCost_le_initial_add_test s g hg hsg hu2 hν t ht hε).trans
    (add_le_add le_rfl (mul_le_mul_right
      (positiveTestCost_le_minEnvelope hν.le s.coefficients t hU hF) _))

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxTameHeatCost
