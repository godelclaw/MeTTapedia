import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionSourceSplit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionSpectralRate

/-!
# Rotation cancels the center-transport debt in the actual filtered work

The complete signed projection material work is combined with the
spectral/center remainder at their original coefficients. The rotation
flux cancels exactly. What remains is all-input subgrid work and a signed
symmetric-strain/spectral integral. Cancellation precedes estimation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionStrainWork

open scoped ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeFilteredStrainDynamics PancakeFrequencyProjectorCommutator
open PancakeLocalInfiniteVelocity PancakeSobolevFiberEnvelope
open LocalProjectionStrainRate LocalHelicityRotationFlux LocalRegularizedHelicityBudget
open LocalProjectionSpectralRate LocalProjectionCoherentRate
open LocalVariableHelicityCenter LocalVorticityEighthMoment
open FiniteBandProjectionAbsorption FilteredProjectionSourceSplit FilteredCoherentProjectionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The center-transport term is absent because it has canceled, not
because it was bounded or dropped. The remaining integral is signed. -/
theorem signedWorkRemainder_eq_strainWork (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (u : FourierVelocity) (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i))
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    signedWorkRemainder ν R P χ u =
      fullSubgridWork (regularization ν R) (normalization R) χ u -
        (LocalWeightedCurlCancellation.weightedStrainSpectralDefect (normalization R) (filteredVelocity χ u) +
          3 * strainMaterialWork (regularization ν R) (filteredVelocity χ u)) / normalization R := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hm := FourierFiniteSupport.summable_fourierMoment P _ hs 4
  have hdχ (q : Wavevector) : modeDot q (filteredVelocity χ u q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, hd q, mul_zero]
  have hrχ := PancakeSpatialStrainEvolution.filteredVelocity_conjugate χ u hχr hr
  rw [signedWorkRemainder_eq_sourceSplit ν R hν P χ hcut C hχ hχr u hu hd hr,
    integral_projectionMaterialRate_eq_strain _ (regularization_pos ν R hν) _ hm hdχ hrχ,
    signedRemainder]
  ring

theorem deriv_correctedEnergy_add_dissipation_le_strainWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν R (filteredVelocity χ (s.coefficients τ))) t +
        (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
        3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      fullSubgridWork (regularization ν R) (normalization R) χ (s.coefficients t) -
        (LocalWeightedCurlCancellation.weightedStrainSpectralDefect (normalization R)
            (filteredVelocity χ (s.coefficients t)) +
          3 * strainMaterialWork (regularization ν R) (filteredVelocity χ (s.coefficients t))) /
          normalization R := by
  have h := deriv_correctedEnergy_add_dissipation_le s hν hB R P hP χ hcut C hχ t ht
  rwa [signedWorkRemainder_eq_strainWork ν R hν P χ hcut C hχ hχr _
    (s.summable_convection t ⟨ht.1.le, ht.2.le⟩) (s.transverse t) (s.reality t)] at h

/-- The actual top-strain coherent contribution has the favorable sign.
The remaining normal-alignment and strain-source work is not bounded. -/
theorem deriv_correctedEnergy_add_dissipation_le_normalWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν R (filteredVelocity χ (s.coefficients τ))) t +
        (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
        3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      fullSubgridWork (regularization ν R) (normalization R) χ (s.coefficients t) -
        (LocalWeightedCurlCancellation.weightedStrainSpectralDefect (normalization R)
            (filteredVelocity χ (s.coefficients t)) +
          3 * (∫ x : T3,
            normalRate (regularization ν R) (filteredVelocity χ (s.coefficients t)) x
              (topStrain (filteredVelocity χ (s.coefficients t)) x) +
            strainSourceRate (regularization ν R) (filteredVelocity χ (s.coefficients t)) x)) /
          normalization R := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hdχ (q : Wavevector) : modeDot q (filteredVelocity χ (s.coefficients t) q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, s.transverse t q, mul_zero]
  have hN := integral_normalRate_add_strainSourceRate_le _ (regularization_pos ν R hν) _
    (FourierFiniteSupport.summable_fourierMoment P _ hs 3) hdχ
    (PancakeSpatialStrainEvolution.filteredVelocity_conjugate χ _ hχr (s.reality t))
  apply (deriv_correctedEnergy_add_dissipation_le_strainWork s hν hB R P hP χ hcut C hχ hχr t ht).trans
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_right (by linarith only [hN]) (normalization_pos R).le

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionStrainWork
