import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointPairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CurlEigenfieldDefect

/-!
# The actual coefficient test in the signed heat-work balance

The commutator is paired with a constructed adjoint of the stretching
variation. The coefficient series is absolutely convergent. Substitution
into the full time identity preserves its sign; no estimate on the
positive-order norm of the test field is assumed in this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatAdjoint

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeBlockReality PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation
open PancakeCurlOutputTail LongitudinalGradientFlux
open ExchangedFluxSeriesBudget ExchangedFluxHeatRepresentation ExchangedFluxHeatBudget
open ExchangedFluxAdjointSeries ExchangedFluxAdjointPairing FourierHeatFlow

/-- The velocity-coefficient test, including the curl and output projection. -/
def heatCoefficientTest (ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) :
    EuclideanSpace ℂ (Fin 3) :=
  coefficientTest (coefficients ν σ u) (projectedFlux 0 (coefficients ν σ u)) q

theorem summable_fourierMoment_commutator {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Summable (fourierMoment 1 (nonlinearCommutator ν σ u)) :=
  CurlEigenfieldDefect.summable_fourierMoment_sub 1 _ _
    (summable_fourierMoment_coefficients hν hσ _ 1
      (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu))
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 _
      (summable_fourierMoment_coefficients hν hσ u 3 hu))

theorem summable_heatCoefficientPairing {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Summable (fun q ↦ ⟪coefficientVec (nonlinearCommutator ν σ u q),
      heatCoefficientTest ν σ u q⟫) :=
  summable_coefficientPairing _ _
    (summable_fourierMoment_coefficients hν hσ u 1
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
    (summable_fourierMoment_commutator hν hσ u hu) _

theorem inner_commutatorVariation_eq_tsum {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    ⟪fluxVariation (coefficients ν σ u) (nonlinearCommutator ν σ u),
      projectedFlux 0 (coefficients ν σ u)⟫ =
    ∑' q, ⟪coefficientVec (nonlinearCommutator ν σ u q), heatCoefficientTest ν σ u q⟫ :=
  inner_fluxVariation_eq_tsum _ _
    (summable_fourierMoment_coefficients hν hσ u 1
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
    (summable_fourierMoment_commutator hν hσ u hu) _

def coefficientWorkDensity (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  ⟪fluxVariation (coefficients ν σ u) (infiniteVelocityRHS 0 (coefficients ν σ u)),
    projectedFlux 0 (coefficients ν σ u)⟫ +
  ∑' q, ⟪coefficientVec (nonlinearCommutator ν σ u q), heatCoefficientTest ν σ u q⟫

theorem heatWorkDensity_eq_coefficientWorkDensity {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    heatWorkDensity ν σ u = coefficientWorkDensity ν σ u := by
  simp only [heatWorkDensity, coefficientWorkDensity, inner_add_left,
    inner_commutatorVariation_eq_tsum hν hσ u hu]

theorem fullGramWork_eq_integral_coefficientWorkDensity {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramWork ν u = ∫ σ : ℝ in Set.Ioi 0, coefficientWorkDensity ν σ u := by
  rw [fullGramWork_eq_integral_heatWorkDensity hν u hu hd hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro σ hσ
  exact heatWorkDensity_eq_coefficientWorkDensity hν.le hσ.le u hu

theorem integrableOn_coefficientWorkDensity {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    IntegrableOn (fun σ ↦ coefficientWorkDensity ν σ u) (Set.Ioi 0) := by
  apply (integrableOn_heatWorkDensity hν u hu hd hr).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact heatWorkDensity_eq_coefficientWorkDensity hν.le hσ.le u hu

open PancakeLocalInfiniteVelocity

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (hν : 0 < ν) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hν hB hg hsg hu

theorem intervalIntegrable_integral_coefficientWorkDensity
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ σ : ℝ in Set.Ioi 0,
      coefficientWorkDensity ν σ (s.coefficients τ)) volume 0 t := by
  apply (intervalIntegrable_fullGramWork s hν hB g hg hsg hu t ht).congr
  intro τ hτ
  have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
    (Set.Icc_subset_Icc le_rfl ht.2) (Set.uIcc_of_le ht.1 ▸ Set.uIoc_subset_uIcc hτ)
  exact fullGramWork_eq_integral_coefficientWorkDensity hν _
    (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)

/-- The actual infinite balance, with the nonlinear coefficient test exposed. -/
theorem full_coefficient_gram_energy_identity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullGramEnergy ν (s.coefficients t) +
      (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
    fullGramEnergy ν u₀ +
      2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
        coefficientWorkDensity ν σ (s.coefficients τ)) := by
  have he : (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) =
      ∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
        coefficientWorkDensity ν σ (s.coefficients τ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    exact fullGramWork_eq_integral_coefficientWorkDensity hν _
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)
  simpa only [he] using full_gram_energy_identity s hν hB g hg hsg hu t ht

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hν hB hg hsg hu in
/-- Smooth physical data construct the solution and its exact adjoint work balance. -/
theorem exists_physical_local_coefficient_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          fullGramEnergy ν (s.coefficients t) +
            (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
          fullGramEnergy ν (torusFourierVelocity f) +
            2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
              coefficientWorkDensity ν σ (s.coefficients τ)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, full_coefficient_gram_energy_identity s hν hB g hg hsg hu⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatAdjoint
