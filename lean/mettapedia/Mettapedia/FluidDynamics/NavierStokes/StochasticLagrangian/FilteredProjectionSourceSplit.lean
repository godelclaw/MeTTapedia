import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionInviscidWork

/-!
# The complete signed source remainder of the filtered correction

Resolved inviscid work is evaluated using its actual material rates. The
subgrid term keeps every output as well as every input: outside the
filter support it cancels the resolved nonlinear RHS, rather than
vanishing separately. All moments used for the resolved spatial calculus
follow from finite support; no high-order bound on the full input is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionSourceSplit

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation PancakeBlockReality
open PancakeSobolevFiberEnvelope PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFrequencyProjectorCommutator InfiniteFilteredEquation
open LocalLowDiffusionBudget LocalProjectionSourceWork LocalVorticityEighthMoment
open LocalProjectionInviscidWork FiniteBandProjectionAbsorption FilteredProjectionAbsorption
open FilteredProjectionNonlinearWork FilteredCoherentProjectionBudget LocalRegularizedHelicityBudget

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullSubgridWork (δ κ : ℝ) (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪correctedGradient δ κ (filteredVelocity χ u) x,
    fullVorticity (subgridForce χ u) x⟫

theorem subgridForce_eq_sub (χ : Wavevector → ℂ) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    subgridForce χ u = filteredVelocity χ (infiniteVelocityRHS 0 u) -
      infiniteVelocityRHS 0 (filteredVelocity χ u) := by
  funext q
  have h := filtered_infiniteVelocityRHS χ u C hχ 0 q (hu q)
  change subgridForce χ u q = filteredVelocity χ (infiniteVelocityRHS 0 u) q -
    infiniteVelocityRHS 0 (filteredVelocity χ u) q
  rw [show filteredVelocity χ (infiniteVelocityRHS 0 u) q = _ from h]
  abel

/-- Outside the filter support, the subgrid and resolved terms cancel.
Neither term is silently removed from the variational pairing. -/
theorem subgridForce_off_support (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i))
    (q : Wavevector) (hq : q ∉ P) :
    subgridForce χ u q = -infiniteVelocityRHS 0 (filteredVelocity χ u) q := by
  rw [subgridForce_eq_sub χ C hχ u hu]
  simp [filteredVelocity, hcut q hq]

theorem summable_fourierMoment_subgridForce (m : ℕ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    Summable (fourierMoment m (subgridForce χ u)) := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  rw [subgridForce_eq_sub χ C hχ u hu]
  exact CurlEigenfieldDefect.summable_fourierMoment_sub m _ _
    (FourierFiniteSupport.summable_fourierMoment P _ (hs _) m)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS m 0 _
      (FourierFiniteSupport.summable_fourierMoment P _ (hs u) (m + 2)))

theorem fullSubgridWork_eq_sub (δ κ : ℝ) (hδ : 0 < δ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    fullSubgridWork δ κ χ u =
      (∫ x : T3, ⟪correctedGradient δ κ (filteredVelocity χ u) x,
        fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 u)) x⟫) -
      ∫ x : T3, ⟪correctedGradient δ κ (filteredVelocity χ u) x,
        fullVorticity (infiniteVelocityRHS 0 (filteredVelocity χ u)) x⟫ := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hm (v : FourierVelocity) (m : ℕ) := FourierFiniteSupport.summable_fourierMoment P _ (hs v) m
  have hf := continuous_fullVorticity _ (hm (infiniteVelocityRHS 0 u) 1)
  have hv := VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 _ (hm u 3)
  have hg := continuous_fullVorticity _ hv
  have ha := continuous_fullVorticity _ (hm u 1)
  have hJ : Continuous (correctedGradient δ κ (filteredVelocity χ u)) :=
    ((ha.norm.pow 6).smul ha).sub ((continuous_projectionGradient δ hδ _ (hm u 2)).const_smul _)
  have hiF : Integrable (fun x : T3 ↦ ⟪correctedGradient δ κ (filteredVelocity χ u) x,
      fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 u)) x⟫) :=
    (hJ.inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (fun x : T3 ↦ ⟪correctedGradient δ κ (filteredVelocity χ u) x,
      fullVorticity (infiniteVelocityRHS 0 (filteredVelocity χ u)) x⟫) :=
    (hJ.inner hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold fullSubgridWork
  rw [subgridForce_eq_sub χ C hχ u hu]
  simp_rw [CurlEigenfieldDefect.fullVorticity_sub _ _ (hm _ 1) hv, inner_sub_right]
  exact integral_sub hiF hiG

theorem nonlinearWork_eq_sourceSplit (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    nonlinearWork ν R P χ u = stretching (filteredVelocity χ u) -
      3 / normalization R * (∫ x : T3,
        projectionMaterialRate (regularization ν R) (filteredVelocity χ u) x) +
      fullSubgridWork (regularization ν R) (normalization R) χ u := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hdχ (q : Wavevector) : modeDot q (filteredVelocity χ u q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, hd q, mul_zero]
  have hi := integral_correctedGradient_inviscidRHS (regularization ν R) (normalization R)
    (regularization_pos ν R hν) _
    (FourierFiniteSupport.summable_fourierMoment P _ hs 5) hdχ
    (PancakeSpatialStrainEvolution.filteredVelocity_conjugate χ u hχr hr)
  rw [nonlinearWork_eq_integral ν R hν P χ hcut C hχ u hu,
    fullSubgridWork_eq_sub _ _ (regularization_pos ν R hν) P χ hcut C hχ u hu, hi]
  ring

/-- Exact remaining debt: subgrid work, projection material work, and
the spectral/center remainder. None of these terms is bounded here. -/
theorem signedWorkRemainder_eq_sourceSplit (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    signedWorkRemainder ν R P χ u =
      fullSubgridWork (regularization ν R) (normalization R) χ u -
      3 / normalization R * (∫ x : T3,
        projectionMaterialRate (regularization ν R) (filteredVelocity χ u) x) -
      signedRemainder (regularization ν R) (normalization R) (filteredVelocity χ u) / normalization R := by
  rw [signedWorkRemainder, nonlinearWork_eq_sourceSplit ν R hν P χ hcut C hχ hχr u hu hd hr]
  ring

theorem deriv_correctedEnergy_add_dissipation_le_sources {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν R (filteredVelocity χ (s.coefficients τ))) t +
        (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
        3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      fullSubgridWork (regularization ν R) (normalization R) χ (s.coefficients t) -
      3 / normalization R * (∫ x : T3,
        projectionMaterialRate (regularization ν R) (filteredVelocity χ (s.coefficients t)) x) -
      signedRemainder (regularization ν R) (normalization R)
        (filteredVelocity χ (s.coefficients t)) / normalization R := by
  have h := deriv_correctedEnergy_add_dissipation_le s hν hB R P hP χ hcut C hχ t ht
  rwa [signedWorkRemainder_eq_sourceSplit ν R hν P χ hcut C hχ hχr _
    (s.summable_convection t ⟨ht.1.le, ht.2.le⟩) (s.transverse t) (s.reality t)] at h

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionSourceSplit
