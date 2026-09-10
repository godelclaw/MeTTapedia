import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalParabolicProjectorEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralBounds
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomParabolicProjectorMotion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPhysicalBottomDiffusion

/-!
# Nonviscous and gradient control of the actual parabolic plane coupling

The second spatial derivative of strain cancels from the bound. The
remaining quantities are the nonviscous transverse coupling and the
square of the actual spatial strain gradient, with their precise gap
powers. The physical-data theorem shares one solution with the signed
bottom-energy balance; it does not pay the source over time or scales.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalParabolicProjectorBound

open scoped ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeFourierMaterialPaths PancakeSpectralClusterDichotomy.SymmetricStrain
open BottomProjectorMotion BottomParabolicProjectorMotion LocalAlignmentForcing
open LocalParabolicProjectorEquation LocalSpatialSpectralBounds LocalPhysicalBottomDiffusion

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def CouplingBound (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : Prop :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  ‖bottomCoupling S (parabolicRate chi modes u nu t x)‖ ≤
    ‖bottomCoupling S (nonviscousRemainder chi modes outputs (u t) x)‖ / bottomGap S +
      4 * nu * strainGradientSquare chi modes (u t) x / bottomGap S ^ 2

theorem ae_ae_couplingBound {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hB : 0 ≤ B) (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      CouplingBound chi modes outputs s.coefficients nu t x := by
  filter_upwards [ae_ae_parabolicRate_equations s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI] with t ht
  filter_upwards [ht] with x hx hg
  exact norm_bottomCoupling_le_of_parabolic_relation _ _ _ _ _ nu _ hg hnu
    (norm_bottomCoupling_mixedGradient_le chi modes (s.coefficients t) x hg) (hx hg).1

/-- The same solution supports every admissible filter's energy balance
and the improved parabolic coupling bound. The exceptional null sets
may depend on the filter and the interior interval. -/
theorem exists_physical_localBottomParabolicControl (nu : ℝ) (hnu : 0 < nu)
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
        ParabolicBalance chi modes s.coefficients nu t x ∧
          CouplingBound chi modes outputs s.coefficients nu t x := by
  obtain ⟨T, hT, B, hB, s, hbalance⟩ :=
    exists_physical_localBottomParabolicBalance nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI
  filter_upwards [hbalance chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI,
    ae_ae_couplingBound s hnu.le chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI]
    with t hb hc
  filter_upwards [hb, hc] with x hx hy hg
  exact ⟨hx hg, hy hg⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalParabolicProjectorBound
