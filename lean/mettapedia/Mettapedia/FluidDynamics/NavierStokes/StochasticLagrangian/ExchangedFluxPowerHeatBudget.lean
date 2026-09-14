import Mettapedia.Analysis.FinitePowerInterpolation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxPowerHeatCost
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxLogarithmicHeatBudget

/-!
# Constructed nonquadratic heat budget and its frequency tradeoff

The signed balance and both pairing bounds hold on the same local solution.
The finite-shell comparison exposes the cost of converting Fourier `8/5`
powers back to square sums. It does not pay either remaining test norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPowerHeatBudget

open scoped ENNReal ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatCommutatorShellBudget FourierHeatCommutatorPowerBudget
open ExchangedFluxHeatDualBudget ExchangedFluxHeatAdjoint
open ExchangedFluxLogarithmicHeatCost ExchangedFluxPowerHeatCost
open ExchangedFluxSeriesBudget LongitudinalGradientFlux
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherDerivativeMoments

/-- Converting the coefficient `8/5` cost to square sums costs a full shell derivative. -/
theorem shell_power_cost_le_derivative_square (n : ℕ) (A : Wavevector → ℝ)
    (hA : ∀ q ∈ IntegerDyadicShell.shell n, 0 ≤ A q) :
    (2 : ℝ) ^ n * (∑ q ∈ IntegerDyadicShell.shell n, A q ^ (8 / 5 : ℝ)) ≤
      (125 : ℝ) ^ (1 / 5 : ℝ) *
        (((2 : ℝ) ^ n) ^ 2 * ∑ q ∈ IntegerDyadicShell.shell n, A q ^ 2) ^ (4 / 5 : ℝ) := by
  have hc : ((IntegerDyadicShell.shell n).card : ℝ) ≤ 125 * ((2 : ℝ) ^ n) ^ 3 := by
    exact_mod_cast IntegerDyadicShell.card_shell_le n
  have hs := FinitePowerInterpolation.sum_eight_fifths_le_card_one_fifth_mul_sum_sq
    (IntegerDyadicShell.shell n) A hA
  calc
    _ ≤ (2 : ℝ) ^ n * ((125 * ((2 : ℝ) ^ n) ^ 3) ^ (1 / 5 : ℝ) *
        (∑ q ∈ IntegerDyadicShell.shell n, A q ^ 2) ^ (4 / 5 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (hs.trans _) (by positivity)
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 125) (by positivity),
        Real.mul_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ n) ^ 2) (by positivity)]
      rw [← Real.rpow_natCast ((2 : ℝ) ^ n) 3, ← Real.rpow_natCast ((2 : ℝ) ^ n) 2,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      have he : (2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (3 * (1 / 5) : ℝ) =
          ((2 : ℝ) ^ n) ^ (2 * (4 / 5) : ℝ) := by
        calc
          _ = ((2 : ℝ) ^ n) ^ (1 : ℝ) * ((2 : ℝ) ^ n) ^ (3 * (1 / 5) : ℝ) := by
            rw [Real.rpow_one]
          _ = ((2 : ℝ) ^ n) ^ (1 + 3 * (1 / 5) : ℝ) :=
            (Real.rpow_add (by positivity) _ _).symm
          _ = _ := by norm_num
      norm_num only [Nat.cast_ofNat]
      calc
        _ = (125 : ℝ) ^ (1 / 5 : ℝ) *
            ((2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (3 * (1 / 5) : ℝ)) *
            (∑ q ∈ IntegerDyadicShell.shell n, A q ^ 2) ^ (4 / 5 : ℝ) := by ring
        _ = _ := by rw [he]; ring

/-- Neither the signed identity nor the new estimate uses an assumed cost budget. -/
theorem exists_physical_local_power_heat_budget (ν : ℝ) (hν : 0 < ν)
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
              ENNReal.ofReal ε⁻¹ * logarithmicTestCost ν s.coefficients t) ∧
          (∀ ε > (0 : ℝ), absolutePairingCost ν s.coefficients t ≤
            ENNReal.ofReal (2 * ε * initialPowerShellBudget ν (torusFourierVelocity f)) +
              ENNReal.ofReal (2 * ε ^ (-3 / 5 : ℝ)) *
                logarithmicTestPowerCost ν s.coefficients t) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  have hu2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  exact ⟨T, hT, B, hB, s, fun t ht ↦
    ⟨full_coefficient_gram_energy_identity s hν hB g hg hsg hu t ht,
      fun ε hε ↦ absolutePairingCost_le_initial_add_logarithmic s g hg hsg hu2 hν t ht hε,
      fun ε hε ↦ absolutePairingCost_le_initial_add_logarithmic_power s g hg hsg hu2 hν t ht hε⟩⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPowerHeatBudget
