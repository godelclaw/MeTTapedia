import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomParabolicSectors

/-!
# Actual bottom-sector damping and the remaining transverse source

The parabolic frame cross term is paid from the bottom gap using the
nonviscous coupling bound. The spatial frame cost lowers the damping by
an explicit gradient-over-gap term. Complementary vorticity gradients
remain in a signed source, not an assumed bounded envelope.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomSectorBudget

open scoped Topology ComplexConjugate RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open LocalBottomEnergy LocalBottomEnergyDiffusion LocalBottomParabolicSectors
open LocalLowDiffusionBudget LocalAlignmentForcing LocalParabolicProjectorBound
open LocalSpatialSpectralBounds BottomProjectorMotion LocalTopPlaneRate

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def parabolicCouplingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  ‖bottomCoupling S (nonviscousRemainder chi modes outputs u x)‖ / bottomGap S +
    4 * nu * strainGradientSquare chi modes u x / bottomGap S ^ 2

def dampingCoefficient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  bottomGap S - 2 * nu * strainGradientSquare chi modes u x / bottomGap S ^ 2

def sectorRemainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := fullVorticity u x
  2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes u x⟫ +
    3 * parabolicCouplingEnvelope chi modes outputs u nu x ^ 2 / bottomGap S *
      ‖expandingPlaneProjector S w‖ ^ 2 - 4 * nu * transverseGradientCross chi modes u x

theorem materialRate_sector_bound (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hnu : 0 ≤ nu) (hu : Summable (fourierMoment 3 (u t)))
    (hdiv : ∀ q, modeDot q (u t q) = 0) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector
      (LocalClusterAnisotropy.frozenStrain chi modes u t x h)) 0)
    (hK : CouplingBound chi modes outputs u nu t x) :
    LocalBottomEnergy.materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x +
        2 * nu * completedGradientSquare chi modes (u t) x +
        dampingCoefficient chi modes (u t) nu x * energy chi modes (u t) x ≤
      sectorRemainder chi modes outputs (u t) nu x := by
  have h := LocalBottomParabolicSectors.materialRate_sub_diffusion_add_damping_le
    chi modes u nu t hnu hu hdiv x hg hP
    (parabolicCouplingEnvelope chi modes outputs (u t) nu x)
    (bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) / 3) (by positivity) hK
  dsimp only at h
  unfold dampingCoefficient sectorRemainder
  dsimp only
  convert! h using 1 <;> ring

theorem half_gap_le_dampingCoefficient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x))
    (hsmall : 4 * nu * strainGradientSquare chi modes u x ≤
      bottomGap (spatialStrain modes (filteredVelocity chi u) x) ^ 3) :
    bottomGap (spatialStrain modes (filteredVelocity chi u) x) / 2 ≤
      dampingCoefficient chi modes u nu x := by
  have hd : 2 * nu * strainGradientSquare chi modes u x /
      bottomGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2 ≤
        bottomGap (spatialStrain modes (filteredVelocity chi u) x) / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hg)).mpr
    nlinarith
  unfold dampingCoefficient
  linarith

/-- Exact signed balance and damping estimate, with the ordinary material
derivative of the actual bottom energy. -/
def SectorControl (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : Prop :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  let L := deriv (fun h ↦ frozenEnergy chi modes u t x h) 0 -
    nu * energyLaplacian chi modes (u t) x + 2 * nu * completedGradientSquare chi modes (u t) x
  HasDerivAt (fun h ↦ frozenEnergy chi modes u t x h) (LocalBottomEnergy.materialRate chi modes u nu t x) 0 ∧
    L = 2 * thirdEigenvalue S * energy chi modes (u t) x + sectorSource chi modes u nu t x ∧
    L + dampingCoefficient chi modes (u t) nu x * energy chi modes (u t) x ≤
      sectorRemainder chi modes outputs (u t) nu x

theorem SectorControl.half_gap_bound {chi : Wavevector → ℂ} {modes outputs : Finset Wavevector}
    {u : ℝ → FourierVelocity} {nu t : ℝ} {x : T3}
    (h : SectorControl chi modes outputs u nu t x)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hsmall : 4 * nu * strainGradientSquare chi modes (u t) x ≤
      bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) ^ 3) :
    deriv (fun h ↦ frozenEnergy chi modes u t x h) 0 - nu * energyLaplacian chi modes (u t) x +
        2 * nu * completedGradientSquare chi modes (u t) x +
        (bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) / 2) * energy chi modes (u t) x ≤
      sectorRemainder chi modes outputs (u t) nu x := by
  have hE : 0 ≤ energy chi modes (u t) x := BottomProjectedEnergy.energy_nonneg _ _
  have hc := mul_le_mul_of_nonneg_right (half_gap_le_dampingCoefficient chi modes (u t) nu x hg hsmall) hE
  have hb := h.2.2
  linarith only [hc, hb]

theorem ae_ae_sectorControl {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
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
      SectorControl chi modes outputs s.coefficients nu t x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_hasDerivAt_frozenEnergy s chi C hchi modes outputs hcut hchir hsub hout hs hk
      hB a b hab hI g hg hSum hu,
    ae_ae_differentiableAt_frozenProjectors s chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI,
    ae_ae_couplingBound s hnu chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI]
    with t ht hd hP hK
  have htm := Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t htm)
  filter_upwards [hd, hP, hK] with x hx hp hk hgap
  refine ⟨hx hgap, ?_, ?_⟩
  · rw [(hx hgap).deriv]
    exact materialRate_sub_diffusion_add_completedSquare_eq chi modes s.coefficients nu t hm x hgap (hp hgap).1
  · rw [(hx hgap).deriv]
    exact materialRate_sector_bound chi modes outputs s.coefficients nu t hnu hm (s.transverse t) x hgap (hp hgap).1 (hk hgap)

theorem exists_physical_localBottomSectorControl (nu : ℝ) (hnu : 0 < nu)
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
        SectorControl chi modes outputs s.coefficients nu t x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI
  exact ae_ae_sectorControl s hnu.le chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI g hg hSum hu

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomSectorBudget
