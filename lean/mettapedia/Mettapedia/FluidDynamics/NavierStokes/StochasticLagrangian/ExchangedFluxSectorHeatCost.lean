import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxSectorSquareSum
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatTestEstimate

/-!
# The Fourier cancellation gain in the accumulated heat cost

The actual selected heat test has a squared geometric factor in its
positive-order cost. The complement remains in an exact coefficient
identity. No estimate for that complement, no dominance of the selected
sector, and no dynamical bound on the output envelope is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSectorHeatCost

open MeasureTheory
open scoped ENNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments FourierHeatFlow LongitudinalGradientFlux
open ExchangedFluxAdjointSectors ExchangedFluxSectorSquareSum ExchangedFluxAdjointWeightedSum
open ExchangedFluxHeatAdjoint ExchangedFluxHeatTestEstimate

def selectedHeatTest (δ η ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) :
    EuclideanSpace ℂ (Fin 3) :=
  selectedTest δ η (coefficients ν σ u) (projectedFlux 0 (coefficients ν σ u)) q

def remainderHeatTest (δ η ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) :
    EuclideanSpace ℂ (Fin 3) :=
  remainderTest δ η (coefficients ν σ u) (projectedFlux 0 (coefficients ν σ u)) q

def selectedHeatCost (δ η ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2) *
    (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (‖selectedHeatTest δ η ν σ (u τ) q‖ ^ 2))

theorem heatTest_eq_selected_add_remainder (δ η : ℝ) {ν σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (q : Wavevector) :
    heatCoefficientTest ν σ u q = selectedHeatTest δ η ν σ u q + remainderHeatTest δ η ν σ u q :=
  coefficientTest_eq_selected_add_remainder δ η _
    (summable_fourierMoment_coefficients hν hσ u 1 hu) _ q

theorem summable_weighted_selectedHeatTest_sq {δ η ν σ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    Summable (fun q ↦ (1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ u q‖ ^ 2) := by
  have h := summable_weighted_selectedTest_sq hδ hη 1 (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [pow_one, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, selectedHeatTest] using h

theorem tsum_weighted_selectedHeatTest_sq_le {δ η ν σ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, (1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ u q‖ ^ 2) ≤
      sectorFactor δ η ^ 2 * heatTestEnvelope ν σ u := by
  have h := tsum_weighted_selectedTest_sq_le hδ hη 1 (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [pow_one, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, selectedHeatTest, heatTestEnvelope, heatOutputNorm] using h

theorem tsum_ofReal_weighted_selectedHeatTest_sq_le {δ η ν σ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ u q‖ ^ 2)) ≤
      ENNReal.ofReal (sectorFactor δ η ^ 2) * ENNReal.ofReal (heatTestEnvelope ν σ u) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (summable_weighted_selectedHeatTest_sq hδ hη hν hσ u hu hF),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (tsum_weighted_selectedHeatTest_sq_le hδ hη hν hσ u hu hF)

theorem selectedHeatCost_le_envelope {δ η ν : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν) (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (u τ) n ^ 2)) :
    selectedHeatCost δ η ν u t ≤ ENNReal.ofReal (sectorFactor δ η ^ 2) *
      (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (heatTestEnvelope ν σ (u τ))) := by
  let f := fun q σ τ ↦ ENNReal.ofReal
    ((1 + ‖frequencyVec q‖) ^ 2 * ‖selectedHeatTest δ η ν σ (u τ) q‖ ^ 2)
  have he : selectedHeatCost δ η ν u t =
      ∑' q, ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ := by
    apply tsum_congr
    intro q
    simp only [f, ENNReal.ofReal_mul (sq_nonneg _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h : selectedHeatCost δ η ν u t ≤
      ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (sectorFactor δ η ^ 2) * ENNReal.ofReal (heatTestEnvelope ν σ (u τ)) := by
    rw [he]
    apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
      (volume.restrict (Set.Ioi 0)) (fun q σ ↦ ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ)).trans
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
      (volume.restrict (Set.Ioc 0 t)) (fun q τ ↦ f q σ τ)).trans
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact tsum_ofReal_weighted_selectedHeatTest_sq_le hδ hη hν hσ.le (u τ) (hu τ hτ) (hF σ hσ τ hτ)
  simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using h

theorem selectedHeatTest_zero_parameters (ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) :
    selectedHeatTest 0 0 ν σ u q = 0 := selectedTest_zero_parameters _ _ _

theorem selectedHeatCost_zero_parameters (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) :
    selectedHeatCost 0 0 ν u t = 0 := by
  simp only [selectedHeatCost, selectedHeatTest_zero_parameters, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    ENNReal.ofReal_zero, lintegral_zero, mul_zero, tsum_zero]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSectorHeatCost
