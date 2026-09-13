import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxModeDynamics
import Mettapedia.Analysis.ODE.DampedGramEnergyEvolution

/-!
# Correlated time budget for the actual exchanged stretching flux

The finite set selects terms of the full interaction series, not terms
in the evolution equation. The source in each slot is the actual full
nonlinear curl. The Gram energy retains all correlations, including
those between triples with equal output frequency. Its dissipation is
the squared spatial L² norm of the sum, with no mode-count factor.

The signed nonlinear Gram work is explicit but not bounded by initial
data here. The finite identities alone do not justify an infinite limit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxGramBudget

open Mettapedia.Analysis
open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeLocalInfiniteVelocity PeriodicGradientFluxTriple LongitudinalExchangeFluxFourier
open FourierVorticityPairDynamics FourierStretchingInteractionDynamics ExchangedFluxModeDynamics

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_tensorCoeff (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i)) (p : TripleIndex) :
    Continuous (fun x ↦ tensorCoeff (u x) p) := by
  have hw := continuous_curl_component u hu
  have hc : Continuous (fun x ↦ pairCross (u x) p.2.1 p.2.2) :=
    continuous_pi (continuous_cross_component _ _ (hw p.2.1) (hw p.2.2))
  exact continuous_pi (fun j ↦ ((hw p.1 j).smul
    ((differenceCLM p).continuous.comp hc)).const_smul (1 / 2 : ℝ))

theorem continuous_sourceTensor (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i))
    (hN : ∀ q i, Continuous (fun x ↦ nonlinearCurl (u x) q i)) (p : TripleIndex) :
    Continuous (fun x ↦ sourceTensor (u x) p) := by
  have hw := continuous_curl_component u hu
  have hc : Continuous (fun x ↦ pairCross (u x) p.2.1 p.2.2) :=
    continuous_pi (continuous_cross_component _ _ (hw p.2.1) (hw p.2.2))
  have hs : Continuous (fun x ↦ pairSource (u x) p.2.1 p.2.2) :=
    continuous_pi (fun i ↦
      (continuous_cross_component _ _ (hN p.2.1) (hw p.2.2) i).add
        (continuous_cross_component _ _ (hw p.2.1) (hN p.2.2) i))
  exact continuous_pi (fun j ↦
    (((hN p.1 j).smul ((differenceCLM p).continuous.comp hc)).add
      ((hw p.1 j).smul ((differenceCLM p).continuous.comp hs))).const_smul (1 / 2 : ℝ))

theorem continuous_mode (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i)) (p : TripleIndex) :
    Continuous (fun x ↦ mode (u x) p) :=
  (tensorModeCLM (tripleFrequency p)).continuous.comp (continuous_tensorCoeff u hu p)

theorem continuous_sourceMode (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i))
    (hN : ∀ q i, Continuous (fun x ↦ nonlinearCurl (u x) q i)) (p : TripleIndex) :
    Continuous (fun x ↦ sourceMode (u x) p) :=
  (tensorModeCLM (tripleFrequency p)).continuous.comp (continuous_sourceTensor u hu hN p)

end Continuity

/-- Correlations are weighted by the reciprocal sum of the input heat rates. -/
def gramEnergy (P : Finset TripleIndex) (ν : ℝ) (u : FourierVelocity) : ℝ :=
  DampedGramEnergy.energy P (interactionDamping ν) (exchangeMode u)

/-- The actual signed nonlinear work, not an assumed budget function. -/
def gramWork (P : Finset TripleIndex) (ν : ℝ) (u : FourierVelocity) : ℝ :=
  DampedGramEnergy.pairing P (interactionDamping ν) (sourceMode u) (exchangeMode u)

theorem gramEnergy_nonneg (P : Finset TripleIndex) {ν : ℝ} (hν : 0 < ν)
    (u : FourierVelocity) (hP : ∀ p ∈ P, p.2.1 ≠ 0) : 0 ≤ gramEnergy P ν u :=
  DampedGramEnergy.energy_nonneg P _ _ (fun p hp ↦ interactionDamping_pos hν p (hP p hp))

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem continuous_exchangeMode (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) : Continuous (fun t ↦ exchangeMode (s.coefficients t) p) := by
  have he (t : ℝ) := mode_eq_exchangeMode (s.coefficients t) p
    (s.transverse t p.2.1) (s.transverse t p.2.2)
  simpa only [he] using continuous_mode s.coefficients s.continuous p

theorem continuousOn_sourceMode (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hB : 0 ≤ B) (p : TripleIndex) :
    ContinuousOn (fun t ↦ sourceMode (s.coefficients t) p) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_sourceMode _ (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) ?_ p
  exact continuous_curl_component _ (FilteredAngularSourceIntegral.continuous_inviscidRHS_component s hB)

/-- Exact time balance for the actual finite partial sum, including the initial endpoint. -/
theorem gram_energy_identity (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hν : 0 < ν) (hB : 0 ≤ B) (P : Finset TripleIndex)
    (hP : ∀ p ∈ P, p.2.1 ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    gramEnergy P ν (s.coefficients t) +
      (∫ τ in (0 : ℝ)..t, ‖∑ p ∈ P, exchangeMode (s.coefficients τ) p‖ ^ 2) =
    gramEnergy P ν u₀ + 2 * (∫ τ in (0 : ℝ)..t, gramWork P ν (s.coefficients τ)) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have h := DampedGramEnergy.energy_identity_of_damped P (interactionDamping ν)
    (fun p hp ↦ interactionDamping_pos hν p (hP p hp))
    (fun τ ↦ exchangeMode (s.coefficients τ)) (fun τ ↦ sourceMode (s.coefficients τ))
    t ht.1 (fun p _ ↦ (continuous_exchangeMode s p).continuousOn)
    (fun p _ ↦ (continuousOn_sourceMode s hB p).mono hsub)
    (fun τ hτ p _ ↦ hasDerivAt_exchangeMode s p τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
  simpa only [s.initial, gramEnergy, gramWork] using h

theorem integral_norm_partialSum_sq_le (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hν : 0 < ν) (hB : 0 ≤ B) (P : Finset TripleIndex)
    (hP : ∀ p ∈ P, p.2.1 ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ‖∑ p ∈ P, exchangeMode (s.coefficients τ) p‖ ^ 2) ≤
      gramEnergy P ν u₀ + 2 * (∫ τ in (0 : ℝ)..t, gramWork P ν (s.coefficients τ)) := by
  have h := gram_energy_identity s hν hB P hP t ht
  have hn := gramEnergy_nonneg P hν (s.coefficients t) hP
  linarith

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxGramBudget
