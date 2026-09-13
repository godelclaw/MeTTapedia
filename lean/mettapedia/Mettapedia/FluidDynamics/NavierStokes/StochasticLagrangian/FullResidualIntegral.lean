import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullAngularSourceAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LowStrainResidualIntegral

/-!
# Initial-data energy inequality with the complete full-field residual

A third absolute moment justifies transferring the filter off the full
vorticity source. For physical initial data the local solution and this
envelope are constructed together. No bound on the signed residual is
assumed or obtained by rewriting it. The cutoff-dependent absorption
requirements of the angular energy are retained verbatim.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullResidualIntegral

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeCurlOutputTail PancakeLocalInfiniteVelocity
open PancakeHigherDerivativeMoments LocalVorticityEighthMoment InfiniteConvectionEnergy
open LocalJointDiffusionBudget FiniteVelocityGradientEnergy
open LowStrainResidualIntegral FullAngularSourceAdjoint

theorem exists_initial_full_residual_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (g : Wavevector → ℝ), (∀ q, 0 ≤ g q) → Summable g →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q) →
      ∀ (κ : ℝ), 0 < κ → ∀ (P Q : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      (∀ q, χ (-q) = conj (χ q)) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → 1 + L * (2 * Real.pi * R) ^ 2 ≤ κ →
      432 * Real.sqrt (derivativeCutoffWeight P χ * kineticEnergy u₀) ≤ ν * κ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        lowStrainIntegratingFactor Q (kineticEnergy u₀) t *
            (meanEnergy (filteredVelocity χ (s.coefficients t)) / 16) +
          (∫ τ in (0 : ℝ)..t, lowStrainIntegratingFactor Q (kineticEnergy u₀) τ *
            ((ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients τ)) +
              6 * ν * radialDissipation (filteredVelocity χ (s.coefficients τ)))) ≤
        meanEnergy (filteredVelocity χ u₀) / 8 +
          ∫ τ in (0 : ℝ)..t, lowStrainIntegratingFactor Q (kineticEnergy u₀) τ *
            fullResidualWork κ P Q χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_initial_residual_inequality
  refine ⟨L, hL, ?_⟩
  intro ν T B u₀ s hν hB g hg hSum hu κ hκ P Q χ hcut C hχ hχr R hP hscale hpay t ht
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have he := hbound s hν hB g hg hSum hu2 κ hκ P Q χ hcut C hχ hχr R hP hscale hpay t ht
  have hint : (∫ τ in (0 : ℝ)..t, lowStrainIntegratingFactor Q (kineticEnergy u₀) τ *
      FiniteLowStrainWork.residualStrainSubgridWork κ Q χ (s.coefficients τ)) =
      ∫ τ in (0 : ℝ)..t, lowStrainIntegratingFactor Q (kineticEnergy u₀) τ *
        fullResidualWork κ P Q χ (s.coefficients τ) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIcc_of_le ht.1] at hτ
      exact ⟨hτ.1, hτ.2.trans ht.2⟩
    dsimp only
    rw [residualStrainSubgridWork_eq_fullResidualWork s κ P Q χ hcut C hχ hχr τ hτT
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτT))]
  rwa [hint] at he

/-- Smooth arbitrary-amplitude periodic data construct the moment envelope
used above; it is not a separately postulated regularity budget. -/
theorem exists_physical_local_full_residual_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ (ν : ℝ), 0 < ν →
      ∀ (f : UnitAddTorus (Fin 3) → VelocityCoefficient),
      (∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 9 (fun x ↦ f x i)) →
      (∀ x i, conj (f x i) = f x i) →
      (∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0) →
      PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0 →
      ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
        ∃ s : LocalInfiniteVelocitySolution ν (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
          ∀ (κ : ℝ), 0 < κ → ∀ (P Q : Finset Wavevector) (χ : Wavevector → ℂ),
          (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
          (∀ q, χ (-q) = conj (χ q)) →
          ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → 1 + L * (2 * Real.pi * R) ^ 2 ≤ κ →
          432 * Real.sqrt (derivativeCutoffWeight P χ *
            kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) ≤ ν * κ →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            lowStrainIntegratingFactor Q (kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) t *
                (meanEnergy (filteredVelocity χ (s.coefficients t)) / 16) +
              (∫ τ in (0 : ℝ)..t,
                lowStrainIntegratingFactor Q (kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) τ *
                  ((ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients τ)) +
                    6 * ν * radialDissipation (filteredVelocity χ (s.coefficients τ)))) ≤
            meanEnergy (filteredVelocity χ (PancakeArbitraryDataBlocks.torusFourierVelocity f)) / 8 +
              ∫ τ in (0 : ℝ)..t,
                lowStrainIntegratingFactor Q (kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) τ *
                  fullResidualWork κ P Q χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_initial_full_residual_inequality
  refine ⟨L, hL, ?_⟩
  intro ν hν f hf hr hd hzero
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, hbound s hν.le hB g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.FullResidualIntegral
