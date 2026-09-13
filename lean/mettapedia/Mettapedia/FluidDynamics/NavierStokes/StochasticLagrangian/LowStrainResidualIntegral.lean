import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LowStrainAngularBalance

/-!
# Initial-endpoint residual budget with low strain paid

Physical initial data construct the local unforced solution and the moment
envelope justifying its kinetic-energy identity. The integrating factor
depends only on the initial kinetic energy and a fixed low-source cutoff.
The retained cutoff and its normalization remain arbitrary subject to the
explicit absorption conditions. The sole residual on the right preserves
the joint sign of strain mismatch and the full subgrid force.

Local integrability of this residual is not a cutoff-uniform bound, nor a
bound approaching a maximal existence endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral

open scoped ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeCurlOutputTail PancakeLocalInfiniteVelocity
open LocalVorticityEighthMoment InfiniteConvectionEnergy FiniteBandAngularEnergy
open FiniteAngularCurlVariation FiniteLowStrainWork LowStrainAngularBalance
open FiniteVelocityGradientEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def lowStrainIntegratingFactor (Q : Finset Wavevector) (E t : ℝ) : ℝ :=
  Real.exp (-(16 * lowStrainGrowthCoefficient Q E) * t)

theorem lowStrainIntegratingFactor_pos (Q : Finset Wavevector) (E t : ℝ) :
    0 < lowStrainIntegratingFactor Q E t := Real.exp_pos _

/-- No source budget is hidden in the constant. Its parameters are only
the initial kinetic energy and the fixed low-source mode set. -/
theorem exists_initial_residual_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (g : Wavevector → ℝ), (∀ q, 0 ≤ g q) → Summable g →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) →
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
            residualStrainSubgridWork κ Q χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_residual_differential_inequality
  refine ⟨L + 768, by positivity, ?_⟩
  intro ν T B u₀ s hν hB g hg hSum hu κ hκ P Q χ hcut C hχ hχr R hP hscale hpay t ht
  have hp := sq_nonneg (2 * Real.pi * R)
  have hscale₁ : 1 + L * (2 * Real.pi * R) ^ 2 ≤ κ := by nlinarith only [hp, hscale]
  have hscale₂ : 48 * (8 * Real.pi * R) ^ 2 ≤ κ := by
    nlinarith only [hscale, mul_nonneg hL.le hp]
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hf := continuous_correctedDensity κ P
    (fun τ : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients τ)) (fun _ ↦ hs _)
    (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
  have hcf := (LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun τ x ↦ correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x) hf).mono hsub
  have hefun : (fun τ ↦ ∫ x : T3, correctedDensity κ (filteredVelocity χ (s.coefficients τ)) x) =
      fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ)) := by
    funext τ
    exact FilteredAngularMean.integral_correctedDensity_eq κ P _ (hs _)
  rw [hefun] at hcf
  have hW := (continuousOn_residualStrainSubgridWork s hB κ P Q χ hcut C hχ hχr).mono hsub
  have hD := (FilteredAngularStrainIntegral.continuousOn_retainedDissipation
    (ν / 4) (6 * ν) s P χ hcut).mono hsub
  have hd (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) t) :=
    FilteredAngularMean.hasDerivAt_correctedEnergy s hB κ P χ hcut τ ⟨hτ.1, hτ.2.trans_le ht.2⟩
  have he := ODE.exp_mul_add_integral_le_of_deriv_le ht.1
    (16 * lowStrainGrowthCoefficient Q (kineticEnergy u₀)) hcf hD hW hd (fun τ hτ ↦ ?_)
  · rw [s.initial] at he
    have hlow := mul_le_mul_of_nonneg_left
      ((correctedEnergy_bounds P (filteredVelocity χ (s.coefficients t)) (hs _) R hP κ hκ hscale₂).1)
      (lowStrainIntegratingFactor_pos Q (kineticEnergy u₀) t).le
    have hupp := correctedEnergy_le κ hκ (filteredVelocity χ u₀)
    dsimp only [lowStrainIntegratingFactor] at hlow ⊢
    linarith only [he, hlow, hupp]
  · have hb := hbound s hν hB g hg hSum hu κ hκ P Q χ hcut C hχ hχr R hP hscale₁ hpay τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩
    rw [(hd τ hτ).deriv] at hb
    simpa only [add_assoc] using hb

/-- The actual physical initial datum supplies the local solution and
common moment envelope. The only unpaid time integral is displayed. -/
theorem exists_physical_local_initial_residual_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ (ν : ℝ), 0 < ν →
      ∀ (f : UnitAddTorus (Fin 3) → VelocityCoefficient),
      (∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 8 (fun x ↦ f x i)) →
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
                  residualStrainSubgridWork κ Q χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_initial_residual_inequality
  refine ⟨L, hL, ?_⟩
  intro ν hν f hf hr hd hzero
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, hbound s hν.le hB g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.LowStrainResidualIntegral
