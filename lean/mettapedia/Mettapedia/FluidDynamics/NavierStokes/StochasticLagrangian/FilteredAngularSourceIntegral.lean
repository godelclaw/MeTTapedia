import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularSourceBalance

/-!
# Initial-endpoint angular energy inequality with the signed full source

Finite output support supplies continuity of every retained spatial jet.
The actual solution supplies continuity of the full nonlinear coefficient
fibers; no global high-order envelope is imposed. Integrating the checked
differential inequality retains positive dissipation and the signed source
integral. That integral is not bounded by initial data here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredAngularSourceIntegral

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation
open PancakePeriodicVorticityEquation PancakeInfiniteFourierTime PancakeLocalInfiniteVelocity
open PancakeFilteredStrainDynamics PancakeFrequencyProjectorCommutator
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FourierFiniteSupport FiniteAngularCurlVariation FilteredAngularMean
open LocalHelicityCenterEvolution
open FiniteAngularSourceWork FilteredAngularSourceBalance FiniteBandAngularEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_inviscidRHS_component {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (q : Wavevector) (i : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ infiniteVelocityRHS 0 (s.coefficients t) q i) := by
  have hv : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      unitTorusViscousVorticityCoeff ν (s.coefficients t) q i) := by
    exact ((s.continuous q i).comp continuous_subtype_val).const_mul _
  have h := (continuous_velocityRHS_component s hB q i).sub hv
  simpa only [infiniteVelocityRHS_eq_zero_add_viscous ν, Pi.add_apply, add_sub_cancel_right] using h

theorem continuousOn_sourceWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) :
    ContinuousOn (fun t ↦ sourceWork κ χ (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hf := continuous_correctedDensityRate κ P
    (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t))
    (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (infiniteVelocityRHS 0 (s.coefficients t)))
    (fun _ ↦ hs _) (fun _ ↦ hs _)
    (fun q _ i ↦ continuous_const.mul ((s.continuous q i).comp continuous_subtype_val))
    (fun q _ i ↦ continuous_const.mul (continuous_inviscidRHS_component s hB q i))
  have h := LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun t x ↦ correctedDensityRate κ (filteredVelocity χ (s.coefficients t))
      (filteredVelocity χ (infiniteVelocityRHS 0 (s.coefficients t))) x) hf
  have he : (fun t ↦ ∫ x : T3, correctedDensityRate κ (filteredVelocity χ (s.coefficients t))
      (filteredVelocity χ (infiniteVelocityRHS 0 (s.coefficients t))) x) =
      fun t ↦ sourceWork κ χ (s.coefficients t) := by
    funext t
    exact integral_correctedDensityRate_eq κ P P _ _ (hs _) (hs _)
  rwa [he] at h

/-- Only the finite retained jets enter this continuity statement. -/
theorem continuousOn_retainedDissipation {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) :
    ContinuousOn (fun t ↦ (ν / 2) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
      6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t))) (Set.Icc (0 : ℝ) T) := by
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
      (filteredVelocity χ (s.coefficients t)) x) hG).const_mul (ν / 2)).add
    ((LocalAlignmentContinuity.continuousOn_spatialIntegral
      (fun t x ↦ radialGradientDensity (filteredVelocity χ (s.coefficients t)) x) hR).const_mul (6 * ν))

/-- The remaining debt is the signed time integral on the right, with all
input frequencies present. This theorem does not pay that debt. -/
theorem exists_initial_energy_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 +
          (∫ τ in (0 : ℝ)..t,
            (ν / 2) * weightedPalinstrophy (filteredVelocity χ (s.coefficients τ)) +
            6 * ν * radialDissipation (filteredVelocity χ (s.coefficients τ))) ≤
        meanEnergy (filteredVelocity χ u₀) / 8 +
          ∫ τ in (0 : ℝ)..t, sourceWork κ χ (s.coefficients τ) := by
  obtain ⟨L, hL, hbound⟩ := exists_coercive_source_threshold
  refine ⟨L + 768, by positivity, ?_⟩
  intro ν T B u₀ s hν hB κ hκ P χ hcut C hχ R hP hscale t ht
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
    exact integral_correctedDensity_eq κ P _ (hs _)
  rw [hefun] at hcf
  have hW := (continuousOn_sourceWork s hB κ P χ hcut).mono hsub
  have hD := (continuousOn_retainedDissipation s P χ hcut).mono hsub
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
  · have h := (hbound s hν hB κ hκ P χ hcut C hχ R hP hscale₁ τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩).2
    rw [(FilteredAngularMean.hasDerivAt_correctedEnergy s hB κ P χ hcut τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩).deriv] at h
    linarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.FilteredAngularSourceIntegral
