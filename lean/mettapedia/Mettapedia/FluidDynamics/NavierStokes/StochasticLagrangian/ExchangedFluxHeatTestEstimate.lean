import Mettapedia.Analysis.LowerIntegralSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointWeightedSum
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatDualBudget

/-!
# Summed output-frequency estimate for the accumulated heat test

The positive-order adjoint cost is bounded by an explicit integral of
weighted curl moments and weighted coefficients of the actual projected
stretching flux. Output square summability is retained as a hypothesis;
control of the resulting integral is not proved here. Lower-integral
inequalities suffice for this upper bound, without asserting Fubini
equalities for a possibly nonmeasurable test.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatTestEstimate

open MeasureTheory
open scoped ENNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeGalerkinKineticEnergy InfiniteConvectionEnergy PancakeLatticeDecayEnvelope
open FourierHeatFlow LongitudinalGradientFlux ExchangedFluxHeatAdjoint ExchangedFluxHeatDualBudget
open ExchangedFluxAdjointWeightedSum

def heatOutputNorm (ν σ : ℝ) (u : FourierVelocity) (n : Wavevector) : ℝ :=
  weightedOutputNorm 2 (projectedFlux 0 (coefficients ν σ u)) n

/-- A regularity-dependent envelope, not a bound in terms of initial kinetic energy. -/
def heatTestEnvelope (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  ((54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm 2 (coefficients ν σ u) k) ^ 2) ^ 2 *
    ∑' n, heatOutputNorm ν σ u n ^ 2

theorem summable_weighted_heatTest_sq {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    Summable (fun q ↦ (1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ u q‖ ^ 2) := by
  have h := summable_weighted_coefficientTest_sq 1 (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [pow_one, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, heatCoefficientTest] using h

theorem tsum_weighted_heatTest_sq_le {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, (1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ u q‖ ^ 2) ≤
      heatTestEnvelope ν σ u := by
  have h := tsum_weighted_coefficientTest_sq_le 1 (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu) (projectedFlux 0 (coefficients ν σ u)) hF
  simpa only [pow_one, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖frequencyVec _‖),
    mul_pow, heatCoefficientTest, heatTestEnvelope, heatOutputNorm] using h

theorem tsum_ofReal_weighted_heatTest_sq_le {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hF : Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2)) :
    (∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ u q‖ ^ 2)) ≤
      ENNReal.ofReal (heatTestEnvelope ν σ u) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (summable_weighted_heatTest_sq hν hσ u hu hF)]
  exact ENNReal.ofReal_le_ofReal (tsum_weighted_heatTest_sq_le hν hσ u hu hF)

theorem positiveTestCost_le_integral_envelope {ν : ℝ} (hν : 0 ≤ ν)
    (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (u τ) n ^ 2)) :
    positiveTestCost ν u t ≤
      ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (heatTestEnvelope ν σ (u τ)) := by
  let f := fun q σ τ ↦ ENNReal.ofReal
    ((1 + ‖frequencyVec q‖) ^ 2 * ‖heatCoefficientTest ν σ (u τ) q‖ ^ 2)
  have he : positiveTestCost ν u t =
      ∑' q, ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ := by
    apply tsum_congr
    intro q
    simp only [f, ENNReal.ofReal_mul (sq_nonneg _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, testSquareIntegral]
  rw [he]
  apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
    (volume.restrict (Set.Ioi 0)) (fun q σ ↦ ∫⁻ τ : ℝ in Set.Ioc 0 t, f q σ τ)).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  apply (Mettapedia.Analysis.LowerIntegralSeries.tsum_lintegral_le
    (volume.restrict (Set.Ioc 0 t)) (fun q τ ↦ f q σ τ)).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  exact tsum_ofReal_weighted_heatTest_sq_le hν hσ.le (u τ) (hu τ hτ) (hF σ hσ τ hτ)

/-- A sufficient envelope criterion; establishing it dynamically is a separate obligation. -/
theorem positiveTestCost_lt_top_of_envelope {ν : ℝ} (hν : 0 ≤ ν)
    (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hF : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Summable (fun n ↦ heatOutputNorm ν σ (u τ) n ^ 2))
    (hI : (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (heatTestEnvelope ν σ (u τ))) < ⊤) :
    positiveTestCost ν u t < ⊤ :=
  (positiveTestCost_le_integral_envelope hν u t hu hF).trans_lt hI

theorem absolutePairingCost_le_initial_add_envelope {ν T B : ℝ} {u₀ : FourierVelocity}
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
        ENNReal.ofReal (heatTestEnvelope ν σ (s.coefficients τ))) := by
  have hu2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hU : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (s.coefficients τ)) :=
    fun τ hτ ↦ hsg.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu τ ⟨hτ.1.le, hτ.2.trans ht.2⟩)
  exact (absolutePairingCost_le_initial_add_test s g hg hsg hu2 hν t ht hε).trans
    (add_le_add le_rfl (mul_le_mul_right
      (positiveTestCost_le_integral_envelope hν.le s.coefficients t hU hF) _))

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatTestEstimate
