import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity

/-!
# Bottom-energy damping on one local solution constructed from physical data

The common third-moment majorant is constructed from the initial field.
The same solution and positive time interval work for every admissible
finite strain filter. The remaining signed source is not integrated here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPhysicalBottomEnergy

open scoped ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open PancakeFourierMaterialPaths PancakeSpectralClusterDichotomy.SymmetricStrain
open LocalBottomEnergy

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_physical_localBottomEnergy (nu : ℝ) (hnu : 0 < nu)
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
      ∀ (a b : ℝ), a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
        0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
        HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients t x h)
          (materialRate chi modes s.coefficients nu t x) 0 ∧
        deriv (fun h ↦ frozenEnergy chi modes s.coefficients t x h) 0 +
          (bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) / 3) *
            energy chi modes (s.coefficients t) x ≤ source chi modes outputs (s.coefficients t) nu x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI
  filter_upwards [ae_ae_hasDerivAt_frozenEnergy s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI g hg hSum hu,
    ae_ae_deriv_frozenEnergy_add_damping_le s chi C hchi modes outputs hcut hchir hsub hout hs hk
      hB a b hab hI g hg hSum hu] with t hderiv hbound
  filter_upwards [hderiv, hbound] with x hx hy hg'
  exact ⟨hx hg', hy hg'⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalPhysicalBottomEnergy
