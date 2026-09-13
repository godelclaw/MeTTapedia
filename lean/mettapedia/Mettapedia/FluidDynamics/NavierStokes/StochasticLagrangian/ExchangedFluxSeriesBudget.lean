import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxModeEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeZeroModeCurlBridge

/-!
# An infinite correlated time identity for the actual stretching flux

Only identically zero inner-curl terms are omitted from the index. The
remaining physical input damping rates have a uniform positive lower
bound. Constructed local envelopes justify the infinite Gram sums and
time integrals, and the sum is identified with the actual projected
inviscid flux. The nonlinear work remains signed and unpaid.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSeriesBudget

open Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity PancakeFrequencyProjectorCommutator
open PancakeHigherDerivativeMoments PancakeZeroModeCurlBridge PancakeInfinitePressureCoefficients
open PeriodicGradientFluxTriple LongitudinalExchangeFluxFourier LongitudinalGradientFlux
open FourierVorticityPairDynamics FourierStretchingInteractionDynamics ExchangedFluxModeDynamics
open ExchangedFluxGramBudget ExchangedFluxModeEnvelope
open PancakeCurlOutputTail

abbrev ActiveTriple := {p : TripleIndex // p.2.1 ≠ 0}

theorem exchangeMode_eq_zero_of_inner_zero (u : FourierVelocity) (p : TripleIndex)
    (hu : ∀ q, modeDot q (u q) = 0) (hp : p.2.1 = 0) : exchangeMode u p = 0 := by
  rw [← mode_eq_exchangeMode u p (hu _) (hu _)]
  have hc : pairCross u p.2.1 p.2.2 = 0 := by
    ext i
    fin_cases i <;> simp [pairCross, hp, fourierCurl_zero, coefficientCross]
  have he : tensorCoeff u p = 0 := by
    funext j
    simp [tensorCoeff, hc]
  rw [mode, he, map_zero]

theorem tsum_active_exchangeMode (u : FourierVelocity) (hu : ∀ q, modeDot q (u q) = 0) :
    ∑' p : ActiveTriple, exchangeMode u p.val = ∑' p : TripleIndex, exchangeMode u p := by
  apply tsum_subtype_eq_of_support_subset
  intro p hp
  change p.2.1 ≠ 0
  intro hz
  exact hp (exchangeMode_eq_zero_of_inner_zero u p hu hz)

theorem damping_lower_bound {ν : ℝ} (hν : 0 < ν) (p : ActiveTriple) :
    ν * (2 * Real.pi) ^ 2 ≤ interactionDamping ν p.val := by
  have hl := one_le_norm_frequencyVec p.property
  have hsq : 1 ≤ ‖frequencyVec p.val.2.1‖ ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ ν * (2 * Real.pi) ^ 2)
  have hk : 0 ≤ modeDamping ν p.val.1 := by unfold modeDamping; positivity
  have hm : 0 ≤ modeDamping ν p.val.2.2 := by unfold modeDamping; positivity
  unfold interactionDamping pairDamping modeDamping at *
  nlinarith

def fullGramEnergy (ν : ℝ) (u : FourierVelocity) : ℝ :=
  DampedGramEnergy.seriesEnergy (fun p : ActiveTriple ↦ interactionDamping ν p.val)
    (fun p : ActiveTriple ↦ exchangeMode u p.val)

def fullGramWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  DampedGramEnergy.seriesPairing (fun p : ActiveTriple ↦ interactionDamping ν p.val)
    (fun p : ActiveTriple ↦ sourceMode u p.val) (fun p : ActiveTriple ↦ exchangeMode u p.val)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (hν : 0 < ν) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hν hB hg hsg hu

theorem intervalIntegrable_fullGramWork (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ fullGramWork ν (s.coefficients τ)) MeasureTheory.volume 0 t := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_summable_mode_source_envelopes s g hg hsg hu
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  apply DampedGramEnergy.intervalIntegrable_seriesPairing _
    (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν) _ _ t ht.1
    (fun p : ActiveTriple ↦ (continuousOn_sourceMode s hB p.val).mono hsub)
    (fun p : ActiveTriple ↦ (continuous_exchangeMode s p.val).continuousOn)
    (fun p : ActiveTriple ↦ b p.val) (fun p : ActiveTriple ↦ a p.val)
    (hb.subtype _) (ha.subtype _)
  · exact fun τ hτ p ↦ (hab τ (hsub hτ) p.val).2
  · intro τ hτ p
    rw [← mode_eq_exchangeMode _ p.val (s.transverse τ _) (s.transverse τ _)]
    exact (hab τ (hsub hτ) p.val).1

theorem full_gram_energy_identity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    fullGramEnergy ν (s.coefficients t) +
      (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
    fullGramEnergy ν u₀ + 2 * (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_summable_mode_source_envelopes s g hg hsg hu
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hx (τ : ℝ) (hτ : τ ∈ Set.Icc 0 t) (p : ActiveTriple) :
      ‖exchangeMode (s.coefficients τ) p.val‖ ≤ a p.val := by
    rw [← mode_eq_exchangeMode _ p.val (s.transverse τ _) (s.transverse τ _)]
    exact (hab τ (hsub hτ) p.val).1
  have hr (τ : ℝ) (hτ : τ ∈ Set.Icc 0 t) (p : ActiveTriple) :
      ‖sourceMode (s.coefficients τ) p.val‖ ≤ b p.val := (hab τ (hsub hτ) p.val).2
  have h := DampedGramEnergy.series_energy_identity_of_damped
    (fun p : ActiveTriple ↦ interactionDamping ν p.val)
    (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν)
    (fun (τ : ℝ) (p : ActiveTriple) ↦ exchangeMode (s.coefficients τ) p.val)
    (fun (τ : ℝ) (p : ActiveTriple) ↦ sourceMode (s.coefficients τ) p.val) t ht.1
    (fun p ↦ (continuous_exchangeMode s p.val).continuousOn)
    (fun p ↦ (continuousOn_sourceMode s hB p.val).mono hsub)
    (fun p : ActiveTriple ↦ a p.val) (fun p : ActiveTriple ↦ b p.val)
    (ha.subtype _) (hb.subtype _) hx hr
    (fun τ hτ p ↦ hasDerivAt_exchangeMode s p.val τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
  have hi : (∫ τ in (0 : ℝ)..t, ‖∑' p : ActiveTriple, exchangeMode (s.coefficients τ) p.val‖ ^ 2) =
      ∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    have hm := summable_fourierMoment_of_le (s.coefficients τ) (by omega : 1 ≤ 3)
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT))
    dsimp only
    rw [tsum_active_exchangeMode _ (s.transverse τ),
      projectedFlux_inviscid_eq_exchangeSeries _ hm (s.reality τ), norm_neg]
  simpa only [fullGramEnergy, fullGramWork, s.initial, hi] using h

omit hB in
theorem fullGramEnergy_nonneg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ fullGramEnergy ν (s.coefficients t) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_summable_mode_source_envelopes s g hg hsg hu
  apply DampedGramEnergy.seriesEnergy_nonneg _ _
    (by positivity : 0 < ν * (2 * Real.pi) ^ 2) (damping_lower_bound hν)
  apply DampedGramEnergy.summable_norm_of_envelope _ (fun p : ActiveTriple ↦ a p.val) (ha.subtype _)
  intro p
  rw [← mode_eq_exchangeMode _ p.val (s.transverse t _) (s.transverse t _)]
  exact (hab t ht p.val).1

/-- Full spatial operator output, with all correlations and no finite-mode cutoff. -/
theorem integral_projectedFlux_sq_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) ≤
      fullGramEnergy ν u₀ + 2 * (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) := by
  have h := full_gram_energy_identity s hν hB g hg hsg hu t ht
  have hn := fullGramEnergy_nonneg s hν g hg hsg hu t ht
  linarith

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hν hB hg hsg hu in
/-- The local solution and every convergence envelope are constructed from physical data. -/
theorem exists_physical_local_flux_budget (ν : ℝ) (hν : 0 < ν)
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
            2 * (∫ τ in (0 : ℝ)..t, fullGramWork ν (s.coefficients τ)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, full_gram_energy_identity s hν hB g hg hsg hu⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSeriesBudget
