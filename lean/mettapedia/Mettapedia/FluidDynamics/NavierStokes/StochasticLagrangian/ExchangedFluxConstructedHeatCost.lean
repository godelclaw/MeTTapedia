import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxWeightedOutput
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxTameHeatCost

/-!
# Heat-cost estimates with the actual output hypothesis discharged

Reality, incompressibility, and the velocity moment envelope construct
the required weighted output series. The physical-data theorem supplies
the same local solution for the exact signed balance and the improved
dual bound. No independent output-summability hypothesis remains.

The remaining envelope integral is not an initial-data dynamical bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxConstructedHeatCost

open MeasureTheory
open scoped ENNReal ComplexConjugate
open Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeBlockReality
open InfiniteConvectionEnergy PancakeLatticeDecayEnvelope LongitudinalGradientFlux
open ExchangedFluxHeatAdjoint ExchangedFluxHeatDualBudget ExchangedFluxHeatTestEstimate
open ExchangedFluxTameHeatCost ExchangedFluxWeightedOutput ExchangedFluxSectorHeatCost
open ExchangedFluxAdjointSectors ExchangedFluxSeriesBudget
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

theorem positiveTestCost_le_minEnvelope_of_velocity {ν : ℝ} (hν : 0 ≤ ν)
    (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hd : ∀ τ ∈ Set.Ioc (0 : ℝ) t, ∀ q, modeDot q (u τ q) = 0)
    (hr : ∀ τ ∈ Set.Ioc (0 : ℝ) t, ∀ q, u τ (-q) = coefficientConjugate (u τ q)) :
    positiveTestCost ν u t ≤ ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (minHeatEnvelope ν σ (u τ)) :=
  positiveTestCost_le_minEnvelope hν u t hu (fun _σ hσ τ hτ ↦
    summable_heatOutputNorm_sq hν hσ.le (u τ) (hu τ hτ) (hd τ hτ) (hr τ hτ))

theorem selectedHeatCost_le_minEnvelope_of_velocity {δ η ν : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hν : 0 ≤ ν)
    (u : ℝ → FourierVelocity) (t : ℝ)
    (hu : ∀ τ ∈ Set.Ioc (0 : ℝ) t, Summable (fourierMoment 3 (u τ)))
    (hd : ∀ τ ∈ Set.Ioc (0 : ℝ) t, ∀ q, modeDot q (u τ q) = 0)
    (hr : ∀ τ ∈ Set.Ioc (0 : ℝ) t, ∀ q, u τ (-q) = coefficientConjugate (u τ q)) :
    selectedHeatCost δ η ν u t ≤ ENNReal.ofReal (sectorFactor δ η ^ 2) *
      (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (minHeatEnvelope ν σ (u τ))) :=
  selectedHeatCost_le_minEnvelope hδ hη hν u t hu (fun _σ hσ τ hτ ↦
    summable_heatOutputNorm_sq hν hσ.le (u τ) (hu τ hτ) (hd τ hτ) (hr τ hτ))

theorem absolutePairingCost_le_initial_add_minEnvelope_of_solution {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (g : Wavevector → ℝ)
    (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (hν : 0 < ν) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal ε * ENNReal.ofReal
        ((2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) * ∑' q, latticeDecayWeight q) +
      ENNReal.ofReal ε⁻¹ * (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
        ENNReal.ofReal (minHeatEnvelope ν σ (s.coefficients τ))) := by
  apply absolutePairingCost_le_initial_add_minEnvelope s g hg hsg hu hν t ht _ hε
  intro σ hσ τ hτ
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.trans ht.2⟩
  exact summable_heatOutputNorm_sq hν.le hσ.le (s.coefficients τ)
    (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)

/-- The weighted output, signed balance, and dual estimate belong to one constructed solution. -/
theorem exists_physical_local_constructed_heat_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ σ ≥ (0 : ℝ), Summable (fun n ↦ heatOutputNorm ν σ (s.coefficients t) n ^ 2)) ∧
          (fullGramEnergy ν (s.coefficients t) +
            (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
          fullGramEnergy ν (torusFourierVelocity f) +
            2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
              coefficientWorkDensity ν σ (s.coefficients τ))) ∧
          (∀ ε > (0 : ℝ), absolutePairingCost ν s.coefficients t ≤
            ENNReal.ofReal ε * ENNReal.ofReal
              ((2 * kineticEnergy (torusFourierVelocity f) ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) *
                ∑' q, latticeDecayWeight q) +
            ENNReal.ofReal ε⁻¹ * (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
              ENNReal.ofReal (minHeatEnvelope ν σ (s.coefficients τ)))) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  refine ⟨T, hT, B, hB, s, fun t ht ↦ ⟨?_, ?_, ?_⟩⟩
  · intro σ hσ
    exact summable_heatOutputNorm_sq hν.le hσ (s.coefficients t)
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.transverse t) (s.reality t)
  · exact full_coefficient_gram_energy_identity s hν hB g hg hsg hu t ht
  · exact fun ε hε ↦ absolutePairingCost_le_initial_add_minEnvelope_of_solution
      s g hg hsg hu hν t ht hε

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxConstructedHeatCost
