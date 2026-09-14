import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxLogarithmicHeatCost
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxConstructedHeatCost

/-!
# The improved heat cost on the constructed physical solution

The new logarithmic weight is bounded by three times the old squared
frequency weight and is asymptotically smaller. One actual local solution
from smooth physical data satisfies both the exact signed balance and
the improved all-scale commutator estimate. No initial-data bound for
the remaining test cost is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxLogarithmicHeatBudget

open scoped ENNReal ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatCommutatorShellBudget ExchangedFluxHeatDualBudget ExchangedFluxHeatAdjoint
open ExchangedFluxLogarithmicHeatCost ExchangedFluxSeriesBudget LongitudinalGradientFlux
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherDerivativeMoments

theorem logarithmicFactor_le_three_mul_two_pow (n : ℕ) :
    ((n : ℝ) + 1) * (n + 2) ≤ 3 * (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; norm_num
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    push_cast
    calc
      _ ≤ 2 * (((n : ℝ) + 1) * (n + 2)) := by nlinarith
      _ ≤ 2 * (3 * (2 : ℝ) ^ n) := by gcongr
      _ = _ := by rw [pow_succ]; ring

theorem logarithmicWeight_le_three_mul_frequencyWeight_sq {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) :
    (2 : ℝ) ^ n * ((n : ℝ) + 1) * (n + 2) ≤ 3 * (1 + ‖frequencyVec q‖) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (logarithmicFactor_le_three_mul_two_pow n)
    (by positivity : 0 ≤ (2 : ℝ) ^ n)
  have hr := radius_le_norm_frequency hq
  have hs : ((2 : ℝ) ^ n) ^ 2 ≤ (1 + ‖frequencyVec q‖) ^ 2 := by
    gcongr
    linarith
  nlinarith

/-- The squared-weight improvement is strict asymptotically in the shell index. -/
theorem logarithmicWeight_ratio_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1) * (n + 2)) / (2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  have h := h2.add ((h1.const_mul 3).add (h0.const_mul 2))
  convert h using 1
  · ext n
    simp only [pow_one, pow_zero]
    ring
  · norm_num

theorem logarithmicTestCost_le_three_mul_positiveTestCost
    (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) :
    logarithmicTestCost ν u t ≤ 3 * positiveTestCost ν u t := by
  let f := fun q ↦ ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2) * testSquareIntegral ν u t q
  calc
    _ ≤ ∑' n : ℕ, ∑ q ∈ IntegerDyadicShell.shell n, 3 * f q := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [shellTestCost, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have h := ENNReal.ofReal_le_ofReal (logarithmicWeight_le_three_mul_frequencyWeight_sq hq)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at h
      norm_num only [ENNReal.ofReal_ofNat] at h
      exact (mul_le_mul_left h _).trans_eq (by dsimp [f]; rw [mul_assoc])
    _ = 3 * (∑' n, ∑ q ∈ IntegerDyadicShell.shell n, f q) := by
      simp only [← Finset.mul_sum, ← ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_right (IntegerDyadicShell.tsum_shells_le f) 3

/-- The signed identity and reduced derivative cost concern the same solution. -/
theorem exists_physical_local_logarithmic_heat_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (fullGramEnergy ν (s.coefficients t) +
            (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
          fullGramEnergy ν (torusFourierVelocity f) +
            2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
              coefficientWorkDensity ν σ (s.coefficients τ))) ∧
          (∀ ε > (0 : ℝ), absolutePairingCost ν s.coefficients t ≤
            ENNReal.ofReal ε * ENNReal.ofReal (initialShellBudget ν (torusFourierVelocity f)) +
              ENNReal.ofReal ε⁻¹ * logarithmicTestCost ν s.coefficients t) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  have hu2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  exact ⟨T, hT, B, hB, s, fun t ht ↦
    ⟨full_coefficient_gram_energy_identity s hν hB g hg hsg hu t ht,
      fun ε hε ↦ absolutePairingCost_le_initial_add_logarithmic s g hg hsg hu2 hν t ht hε⟩⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxLogarithmicHeatBudget
