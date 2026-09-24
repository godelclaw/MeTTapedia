import Mettapedia.Analysis.ODE.DampedGramHeatRepresentation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VelocityRHSMoments

/-!
# Heat representation of the full stretching energy and signed work

The full Gram energy is the integral of the squared projected inviscid
flux evaluated at auxiliary heat-smoothed velocities. Its nonlinear work
pairs that flux with the termwise variation in the smoothed actual
nonlinear rate. The discrepancy from recomputing the rate after smoothing
is retained as a convergent commutator insertion.

These identities do not bound nonlinear work by initial data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatRepresentation

open scoped RealInnerProductSpace
open MeasureTheory
open Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeIndexedFourierMoments PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeBlockReality
open PancakeCoefficientLimitEquation PeriodicGradientFluxTriple FourierVorticityPairDynamics
open FourierStretchingInteractionDynamics LongitudinalExchangeFluxFourier LongitudinalGradientFlux
open ExchangedFluxModeDynamics ExchangedFluxModeEnvelope ExchangedFluxSeriesBudget
open ExchangedFluxVariation ExchangedFluxHeatVariation FourierHeatFlow

local notation "H" => UnitTorusGradientProjection.TensorL2 (Fin 3) (EuclideanSpace ℝ (Fin 3))

theorem summable_norm_curl (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun q ↦ ‖fourierCurl u q‖) := by
  have h := summable_norm_curlCoefficients id u (by simpa only [indexedFirstMoment_id] using hu)
  exact h

theorem summable_norm_mode (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun p : TripleIndex ↦ ‖mode u p‖) :=
  (summable_cubicEnvelope (fun q ↦ ‖fourierCurl u q‖) (fun _ ↦ norm_nonneg _)
    (summable_norm_curl u hu)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_mode_le_cubicEnvelope u _ (fun _ ↦ le_rfl))

theorem summable_norm_exchangeMode (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    Summable (fun p : TripleIndex ↦ ‖exchangeMode u p‖) := by
  simpa only [mode_eq_exchangeMode u _ (hd _) (hd _)] using summable_norm_mode u hu

theorem summable_norm_sourceMode (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Summable (fun p : TripleIndex ↦ ‖sourceMode u p‖) := by
  have hw := summable_norm_curl u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hn := summable_norm_curl (infiniteVelocityRHS 0 u)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu)
  exact (summable_sourceEnvelope (fun q ↦ ‖fourierCurl u q‖) (fun q ↦ ‖nonlinearCurl u q‖)
    (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _) hw hn).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (norm_sourceMode_le_sourceEnvelope u _ _ (fun _ ↦ le_rfl) (fun _ ↦ le_rfl))

/-- The convergent termwise variation of the projected inviscid flux. -/
def fluxVariation (u v : FourierVelocity) : H :=
  -∑' p : ActiveTriple, variationMode u v p.val

theorem decay_exchangeSeries_eq_neg_projectedFlux {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    DampedGramEnergy.decaySeries (fun p : ActiveTriple ↦ interactionDamping ν p.val)
      (fun p ↦ exchangeMode u p.val) σ = -projectedFlux 0 (coefficients ν σ u) := by
  unfold DampedGramEnergy.decaySeries
  simp_rw [← exchangeMode_heat ν σ u hd]
  rw [tsum_active_exchangeMode _ (coefficients_transverse ν σ u hd),
    projectedFlux_inviscid_eq_exchangeSeries _ (summable_fourierMoment_coefficients hν.le hσ u 1 hu)
      (coefficients_reality ν σ u hr), neg_neg]

theorem decay_sourceSeries_eq_neg_fluxVariation (ν σ : ℝ) (u : FourierVelocity) :
    DampedGramEnergy.decaySeries (fun p : ActiveTriple ↦ interactionDamping ν p.val)
      (fun p ↦ sourceMode u p.val) σ =
    -fluxVariation (coefficients ν σ u) (coefficients ν σ (infiniteVelocityRHS 0 u)) := by
  simp only [DampedGramEnergy.decaySeries, fluxVariation, neg_neg,
    sourceMode_eq_variationMode, variationMode_heat]

theorem fullGramEnergy_eq_integral_heat_flux_sq {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramEnergy ν u = ∫ σ : ℝ in Set.Ioi 0, ‖projectedFlux 0 (coefficients ν σ u)‖ ^ 2 := by
  rw [fullGramEnergy, DampedGramEnergy.seriesEnergy_eq_integral_norm_decaySeries_sq _
    _ (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν)
    ((summable_norm_exchangeMode u hu hd).subtype _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [decay_exchangeSeries_eq_neg_projectedFlux hν hσ.le u hu hd hr, norm_neg]

theorem fullGramWork_eq_integral_heat_variation {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramWork ν u = ∫ σ : ℝ in Set.Ioi 0,
      ⟪fluxVariation (coefficients ν σ u) (coefficients ν σ (infiniteVelocityRHS 0 u)),
        projectedFlux 0 (coefficients ν σ u)⟫ := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  rw [fullGramWork, DampedGramEnergy.seriesPairing_eq_integral_decay_inner _
    _ _ (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν)
    ((summable_norm_sourceMode u hu).subtype _) ((summable_norm_exchangeMode u hu1 hd).subtype _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [decay_exchangeSeries_eq_neg_projectedFlux hν hσ.le u hu1 hd hr,
    decay_sourceSeries_eq_neg_fluxVariation, inner_neg_neg]

theorem summable_commutator_variation {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Summable (fun p : ActiveTriple ↦
      variationMode (coefficients ν σ u) (nonlinearCommutator ν σ u) p.val) := by
  have hd := (DampedGramEnergy.summable_norm_decay
    (fun p : ActiveTriple ↦ interactionDamping ν p.val) (fun p ↦ sourceMode u p.val)
    (fun p ↦ (by positivity : 0 < ν * (2 * Real.pi) ^ 2).le.trans (damping_lower_bound hν p))
    ((summable_norm_sourceMode u hu).subtype _) hσ).of_norm
  have hs : Summable (fun p : ActiveTriple ↦ sourceMode (coefficients ν σ u) p.val) :=
    ((summable_norm_sourceMode (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν.le hσ u 3 hu)).subtype _).of_norm
  have he (p : ActiveTriple) :
      variationMode (coefficients ν σ u) (nonlinearCommutator ν σ u) p.val =
      Real.exp (-interactionDamping ν p.val * σ) • sourceMode u p.val -
        sourceMode (coefficients ν σ u) p.val := by
    rw [decayed_source_eq_resolved_add_commutator]
    abel
  simpa only [he] using hd.sub hs

set_option synthInstance.maxHeartbeats 80000 in
/-- The full source split is justified before pairing or taking absolute values. -/
theorem heat_fluxVariation_eq_resolved_add_commutator {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    fluxVariation (coefficients ν σ u) (coefficients ν σ (infiniteVelocityRHS 0 u)) =
      fluxVariation (coefficients ν σ u) (infiniteVelocityRHS 0 (coefficients ν σ u)) +
      fluxVariation (coefficients ν σ u) (nonlinearCommutator ν σ u) := by
  letI : T2Space H := inferInstance
  have hs : Summable (fun p : ActiveTriple ↦ sourceMode (coefficients ν σ u) p.val) :=
    ((summable_norm_sourceMode (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν.le hσ u 3 hu)).subtype _).of_norm
  have hc := summable_commutator_variation hν hσ u hu
  have he : coefficients ν σ (infiniteVelocityRHS 0 u) =
      infiniteVelocityRHS 0 (coefficients ν σ u) + nonlinearCommutator ν σ u := by
    unfold nonlinearCommutator
    abel
  unfold fluxVariation
  rw [he]
  simp_rw [variationMode_add, ← sourceMode_eq_variationMode]
  rw [hs.tsum_add hc, neg_add_rev, add_comm]

theorem fullGramWork_eq_integral_resolved_add_commutator {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    fullGramWork ν u = ∫ σ : ℝ in Set.Ioi 0,
      ⟪fluxVariation (coefficients ν σ u) (infiniteVelocityRHS 0 (coefficients ν σ u)) +
          fluxVariation (coefficients ν σ u) (nonlinearCommutator ν σ u),
        projectedFlux 0 (coefficients ν σ u)⟫ := by
  rw [fullGramWork_eq_integral_heat_variation hν u hu hd hr]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [heat_fluxVariation_eq_resolved_add_commutator hν hσ.le u hu]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatRepresentation
