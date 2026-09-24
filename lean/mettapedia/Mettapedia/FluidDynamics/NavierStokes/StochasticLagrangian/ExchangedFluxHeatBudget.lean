import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatRepresentation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorKernel

/-!
# Signed heat-work balance along the actual Navier--Stokes solution

Auxiliary heat time is integrated inside physical solution time. The
resolved nonlinear rate and its actual heat commutator stay in one signed
pairing. All integrability hypotheses follow from constructed local
Fourier envelopes; no bound on the accumulated nonlinear work is assumed
or proved here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatBudget

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeBlockReality PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation
open PancakeCurlOutputTail
open PancakePeriodicVorticityEquation FourierStretchingInteractionDynamics
open LongitudinalGradientFlux LongitudinalExchangeFluxFourier ExchangedFluxModeDynamics
open ExchangedFluxSeriesBudget ExchangedFluxHeatRepresentation
open FourierHeatFlow FourierHeatCommutatorKernel

def heatWorkDensity (ν σ : ℝ) (u : FourierVelocity) : ℝ :=
  ⟪fluxVariation (coefficients ν σ u) (infiniteVelocityRHS 0 (coefficients ν σ u)) +
      fluxVariation (coefficients ν σ u) (nonlinearCommutator ν σ u),
    projectedFlux 0 (coefficients ν σ u)⟫

theorem fullGramWork_eq_integral_heatWorkDensity {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramWork ν u = ∫ σ : ℝ in Set.Ioi 0, heatWorkDensity ν σ u :=
  fullGramWork_eq_integral_resolved_add_commutator hν u hu hd hr

theorem integrableOn_heatWorkDensity {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    IntegrableOn (fun σ ↦ heatWorkDensity ν σ u) (Set.Ioi 0) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have h := DampedGramEnergy.integrableOn_decay_inner
    (fun p : ActiveTriple ↦ interactionDamping ν p.val)
    (fun p ↦ sourceMode u p.val) (fun p ↦ exchangeMode u p.val)
    (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν)
    ((summable_norm_sourceMode u hu).subtype _) ((summable_norm_exchangeMode u hu1 hd).subtype _)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [decay_exchangeSeries_eq_neg_projectedFlux hν hσ.le u hu1 hd hr,
    decay_sourceSeries_eq_neg_fluxVariation, inner_neg_neg,
    heat_fluxVariation_eq_resolved_add_commutator hν hσ.le u hu]
  rfl

/-- The pressure-corrected signed Duhamel input is substituted without an absolute value. -/
theorem heatWorkDensity_eq_duhamel {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    heatWorkDensity ν σ u =
      ⟪fluxVariation (coefficients ν σ u) (infiniteVelocityRHS 0 (coefficients ν σ u)) +
          fluxVariation (coefficients ν σ u)
            (fun q ↦ lerayMode q ((-unitTorusDerivativePhase) • duhamelConvection ν σ u q)),
        projectedFlux 0 (coefficients ν σ u)⟫ := by
  have he : nonlinearCommutator ν σ u =
      fun q ↦ lerayMode q ((-unitTorusDerivativePhase) • duhamelConvection ν σ u q) :=
    funext (nonlinearCommutator_eq_duhamel hν.le hσ u hu)
  rw [heatWorkDensity, he]

open PancakeLocalInfiniteVelocity

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (hν : 0 < ν) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hν hB hg hsg hu

theorem intervalIntegrable_integral_heatWorkDensity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ σ : ℝ in Set.Ioi 0, heatWorkDensity ν σ (s.coefficients τ))
      volume 0 t := by
  apply (intervalIntegrable_fullGramWork s hν hB g hg hsg hu t ht).congr
  intro τ hτ
  have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
    (Set.Icc_subset_Icc le_rfl ht.2) (Set.uIcc_of_le ht.1 ▸ Set.uIoc_subset_uIcc hτ)
  exact fullGramWork_eq_integral_heatWorkDensity hν _
    (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)

/-- The full infinite stretching balance with both nonlinear heat channels exposed. -/
theorem full_heat_gram_energy_identity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullGramEnergy ν (s.coefficients t) +
      (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
    fullGramEnergy ν u₀ +
      2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0, heatWorkDensity ν σ (s.coefficients τ)) := by
  have he : (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) =
      ∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0, heatWorkDensity ν σ (s.coefficients τ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    exact fullGramWork_eq_integral_heatWorkDensity hν _
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT)) (s.transverse τ) (s.reality τ)
  simpa only [he] using full_gram_energy_identity s hν hB g hg hsg hu t ht

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hν hB hg hsg hu in
/-- Physical data construct the local solution and the complete signed heat balance. -/
theorem exists_physical_local_heat_budget (ν : ℝ) (hν : 0 < ν)
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
              heatWorkDensity ν σ (s.coefficients τ)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, full_heat_gram_energy_identity s hν hB g hg hsg hu⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatBudget
