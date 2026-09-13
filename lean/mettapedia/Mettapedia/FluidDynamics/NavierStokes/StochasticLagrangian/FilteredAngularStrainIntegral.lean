import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AngularTransportAbsorption
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransportContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularSourceIntegral

/-!
# Initial-endpoint angular balance after transport absorption

The initial energy pays transport through a fixed, explicitly
cutoff-dependent normalization. The remaining time integral is the signed
strain work plus the complete subgrid pairing, not a sum of absolute
channel bounds. Its cutoff-uniform dynamical control is not asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredAngularStrainIntegral

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeFilteredStrainDynamics PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open LocalVorticityEighthMoment InfiniteConvectionEnergy FiniteBandAngularEnergy
open FiniteAngularCurlVariation FiniteAngularInviscidWork FiniteAngularTransport
open FilteredAngularSourceBalance FilteredAngularSourceIntegral
open FiniteVelocityGradientEnergy AngularTransportAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def strainSubgridWork (κ : ℝ) (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  stretching (filteredVelocity χ u) - (3 / κ) * angularStrainWork (filteredVelocity χ u) +
    fullSubgridWork κ χ u

theorem strainSubgridWork_solution_eq {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    strainSubgridWork κ χ (s.coefficients t) = sourceWork κ χ (s.coefficients t) -
      (3 / κ) * deformationIntegral (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (s.coefficients t)) := by
  rw [sourceWork_solution_eq s κ P χ hcut C hχ hχr t ht]
  unfold strainSubgridWork
  ring

theorem continuousOn_strainSubgridWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q)) :
    ContinuousOn (fun t ↦ strainSubgridWork κ χ (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  have hW := continuousOn_sourceWork s hB κ P χ hcut
  have hD := FiniteAngularTransportContinuity.continuousOn_deformationIntegral s P χ hcut
  exact (hW.sub (hD.const_mul (3 / κ))).congr
    (fun t ht ↦ strainSubgridWork_solution_eq s κ P χ hcut C hχ hχr t ht)

theorem continuousOn_retainedDissipation (a b : ℝ) {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) :
    ContinuousOn (fun t ↦ a * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
      b * radialDissipation (filteredVelocity χ (s.coefficients t))) (Set.Icc (0 : ℝ) T) := by
  have hs (t : Set.Icc (0 : ℝ) T) (q : Wavevector) (hq : q ∉ P) :
      filteredVelocity χ (s.coefficients t) q = 0 := by simp [filteredVelocity, hcut q hq]
  have hc (q : Wavevector) (_hq : q ∈ P) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t) q i) :=
    continuous_const.mul ((s.continuous q i).comp continuous_subtype_val)
  have ha := FilteredProjectionMean.continuous_fullVorticity P _ hs hc
  have hD := FiniteAngularCurlVariation.continuous_fullCurlGradient P _ hs hc
  have hG := (ha.norm.pow 6).mul (continuous_finsetSum Finset.univ (fun j _ ↦ (hD j).norm.pow 2))
  have hR := (ha.norm.pow 4).mul (continuous_finsetSum Finset.univ (fun j _ ↦ (ha.inner (hD j)).pow 2))
  exact ((LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun t x ↦ GaussianRootWeightedIncrement.weightedPalinstrophyDensity
      (filteredVelocity χ (s.coefficients t)) x) hG).const_mul a).add
    ((LocalAlignmentContinuity.continuousOn_spatialIntegral
      (fun t x ↦ radialGradientDensity (filteredVelocity χ (s.coefficients t)) x) hR).const_mul b)

/-- Transport is paid, but the signed strain/subgrid time integral is not. -/
theorem exists_initial_energy_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (g : Wavevector → ℝ), (∀ q, 0 ≤ g q) → Summable g →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) →
      ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      (∀ q, χ (-q) = conj (χ q)) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
      432 * Real.sqrt (derivativeCutoffWeight P χ * kineticEnergy u₀) ≤ ν * κ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 +
          (∫ τ in (0 : ℝ)..t,
            (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients τ)) +
            6 * ν * radialDissipation (filteredVelocity χ (s.coefficients τ))) ≤
        meanEnergy (filteredVelocity χ u₀) / 8 +
          ∫ τ in (0 : ℝ)..t, strainSubgridWork κ χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_coercive_strain_subgrid_threshold
  refine ⟨L + 768, by positivity, ?_⟩
  intro ν T B u₀ s hν hB g hg hSum hu κ hκ P χ hcut C hχ hχr R hP hscale hpay t ht
  have hp := sq_nonneg (2 * Real.pi * R)
  have hscale₁ : L * (2 * Real.pi * R) ^ 2 ≤ κ := by nlinarith only [hp, hscale]
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
  have hW := (continuousOn_strainSubgridWork s hB κ P χ hcut C hχ hχr).mono hsub
  have hD := (continuousOn_retainedDissipation (ν / 4) (6 * ν) s P χ hcut).mono hsub
  have he := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1 hcf
    (fun τ hτ ↦ (FilteredAngularMean.hasDerivAt_correctedEnergy s hB κ P χ hcut τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩).hasDerivWithinAt)
    ((hW.sub hD).integrableOn_Icc) (fun τ hτ ↦ ?_)
  · rw [intervalIntegral.integral_sub (hW.intervalIntegrable_of_Icc ht.1)
      (hD.intervalIntegrable_of_Icc ht.1), s.initial] at he
    have hlow := (correctedEnergy_bounds P (filteredVelocity χ (s.coefficients t))
      (hs (s.coefficients t)) R hP κ hκ hscale₂).1
    have hupp := correctedEnergy_le κ hκ (filteredVelocity χ u₀)
    linarith only [he, hlow, hupp]
  · have h := (hbound s hν hB g hg hSum hu κ hκ P χ hcut C hχ hχr R hP hscale₁ hpay τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩).2
    rw [(FilteredAngularMean.hasDerivAt_correctedEnergy s hB κ P χ hcut τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩).deriv] at h
    change _ ≤ strainSubgridWork κ χ (s.coefficients τ) at h
    linarith only [h]

/-- Physical data construct the common moment envelope used to justify the
energy identity. Only the remaining signed source integral is unpaid. -/
theorem exists_physical_local_initial_energy_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ (ν : ℝ), 0 < ν →
      ∀ (f : UnitAddTorus (Fin 3) → VelocityCoefficient),
      (∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 8 (fun x ↦ f x i)) →
      (∀ x i, conj (f x i) = f x i) →
      (∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0) →
      PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0 →
      ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
        ∃ s : LocalInfiniteVelocitySolution ν (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
          ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
          (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
          (∀ q, χ (-q) = conj (χ q)) →
          ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
          432 * Real.sqrt (derivativeCutoffWeight P χ *
            kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f)) ≤ ν * κ →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 +
              (∫ τ in (0 : ℝ)..t,
                (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients τ)) +
                6 * ν * radialDissipation (filteredVelocity χ (s.coefficients τ))) ≤
            meanEnergy (filteredVelocity χ (PancakeArbitraryDataBlocks.torusFourierVelocity f)) / 8 +
              ∫ τ in (0 : ℝ)..t, strainSubgridWork κ χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_initial_energy_inequality
  refine ⟨L, hL, ?_⟩
  intro ν hν f hf hr hd hzero
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, hbound s hν.le hB g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.FilteredAngularStrainIntegral
