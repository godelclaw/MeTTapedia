import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentSourceLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentBudget

/-!
# Actual initial-data alignment budget without auxiliary source smoothing

Dominated convergence removes the source parameter while the energy
regularizer remains fixed and positive. No continuity of the limiting
source through spectral collisions is assumed. This strengthens the
local estimate but does not pay the remaining nonlinear source globally.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLimitingAlignmentBudget

open scoped Topology ComplexConjugate
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open LocalAlignmentForcing LocalMeanAlignmentBalance LocalLimitingAlignmentSource
open SpectralAnisotropyLimit LocalAlignmentSourceLimit

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem meanEnergy_add_integral_residual_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hT : 0 < T) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (delta : ℝ) (hd : 0 < delta) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy chi modes (s.coefficients t) delta +
      (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hlim := (intervalIntegrable_and_tendsto_integral_source s g hg hSum hu2 chi C hchi
    modes outputs delta t ht).2
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_const_nhds.add hlim)
  intro n
  exact LocalDepletedAlignmentBudget.meanEnergy_add_integral_residual_le_initial
    s hnu hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd
    (approximationParameter n) (approximationParameter_pos n) hT t ht

/-- A single local solution for every admissible finite strain filter,
with the auxiliary source parameter removed from the conclusion. -/
theorem exists_physical_localLimitingAlignmentBudget (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hdiv : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∀ (chi : Wavevector → ℂ) (C : ℝ), (∀ q, ‖chi q‖ ≤ C) →
      ∀ modes outputs : Finset Wavevector, (∀ q, q ∉ modes → chi q = 0) →
      (∀ q, chi (-q) = conj (chi q)) → modes ⊆ outputs →
      (∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs) →
      (∀ k, -k ∈ modes ↔ k ∈ modes) → (∀ k ∈ modes, frequencyVec k ≠ 0) →
      ∀ delta > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
      meanEnergy chi modes (s.coefficients t) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        4 * strainGradientCutoffWeight modes chi * kineticEnergy (torusFourierVelocity f) ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  exact meanEnergy_add_integral_residual_le_initial s hnu hT hB g hg hSum hu chi C hchi modes outputs
    hcut hchir hsub hout hs hk delta hd t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalLimitingAlignmentBudget
