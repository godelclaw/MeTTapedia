import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSourceExcess

/-!
# Physical alignment energy after diffusion and source absorption

One quarter of the integrated coherent residual remains on the left.
The right side contains only excess diffusion, excess nonviscous source,
and the original signed mismatch and energy-regularizer terms. The
construction works simultaneously for all admissible finite filters on
one actual local solution from arbitrary admissible periodic data.

The result is a local energy inequality, not a bound uniform in the filter,
energy regularizer, or maximal existence time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalExcessAlignmentEnergy

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeHigherLocalVelocity LocalMeanAlignmentBalance LocalLowDiffusionBudget
open LocalAlignmentForcing (residual)
open LocalExcessDiffusionEnergy LocalSourceExcess

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem meanEnergy_add_quarter_integral_residual_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
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
      (1 / 4 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes u₀ delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, excessCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, forcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hE := meanEnergy_add_half_integral_residual_le_initial
    s hnu hT hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  have hF := integral_source_le_quarter_residual_add_excess
    s g hg hSum hu2 chi C hchi modes outputs delta t ht
  linarith only [hE, hF]

/-- Arbitrary admissible data produce one solution satisfying the combined
excess budget for every admissible filter and positive energy regularizer. -/
theorem exists_physical_localExcessAlignmentEnergy (nu : ℝ) (hnu : 0 < nu)
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
        (1 / 4 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) ≤
      meanEnergy chi modes (torusFourierVelocity f) delta +
        (∫ τ in (0 : ℝ)..t, ∫ x : T3, excessCost chi modes (s.coefficients τ) delta nu x) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, forcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht
  exact meanEnergy_add_quarter_integral_residual_le_initial
    s hnu hT hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk delta hd t ht

end Mettapedia.FluidDynamics.NavierStokes.LocalExcessAlignmentEnergy
