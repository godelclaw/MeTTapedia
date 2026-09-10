import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomEnergyDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity

/-!
# Bottom-energy parabolic balance on one physical local NS solution

The material derivative, spatial Laplacian, and projected gradient square
all come from the constructed fields. The same physical-data solution
works for every admissible finite filter. The signed parabolic source is
not assumed bounded and no time-integrated estimate is inferred here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPhysicalBottomDiffusion

open scoped ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open PancakeFourierMaterialPaths PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalBottomEnergy LocalBottomEnergyDiffusion

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Both the exact signed balance and its trace-free damping consequence. -/
def ParabolicBalance (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : Prop :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  let L := deriv (fun h ↦ frozenEnergy chi modes u t x h) 0 -
    nu * energyLaplacian chi modes (u t) x + 2 * nu * projectedGradientSquare chi modes (u t) x
  HasDerivAt (fun h ↦ frozenEnergy chi modes u t x h) (materialRate chi modes u nu t x) 0 ∧
    L = 2 * thirdEigenvalue S * energy chi modes (u t) x + parabolicSource chi modes u nu t x ∧
    L + (4 / 3 : ℝ) * bottomGap S * energy chi modes (u t) x ≤ parabolicSource chi modes u nu t x

theorem ae_ae_parabolicBalance {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hB : 0 ≤ B) (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      ParabolicBalance chi modes s.coefficients nu t x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_hasDerivAt_frozenEnergy s chi C hchi modes outputs hcut hchir hsub hout hs hk
      hB a b hab hI g hg hSum hu] with t ht hderiv
  have htm := Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t htm)
  filter_upwards [hderiv] with x hx hgap
  refine ⟨hx hgap, ?_, ?_⟩
  · rw [(hx hgap).deriv]
    exact materialRate_sub_diffusion_add_gradient_eq chi modes s.coefficients nu t hm x hgap
  · rw [(hx hgap).deriv]
    exact materialRate_sub_diffusion_add_damping_le chi modes s.coefficients nu t hm (s.transverse t) x hgap

theorem exists_physical_localBottomParabolicBalance (nu : ℝ) (hnu : 0 < nu)
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
        ParabolicBalance chi modes s.coefficients nu t x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI
  exact ae_ae_parabolicBalance s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI g hg hSum hu

end Mettapedia.FluidDynamics.NavierStokes.LocalPhysicalBottomDiffusion
