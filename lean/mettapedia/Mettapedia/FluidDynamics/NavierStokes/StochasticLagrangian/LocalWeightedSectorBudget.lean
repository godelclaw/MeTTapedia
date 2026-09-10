import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedSectorBalance

/-!
# Actual coupled-sector damping estimate

For each constant weight `0 < θ ≤ 1`, the vorticity-gradient cross term is
absorbed by the two-sector dissipation. The price is `(1-θ)/θ` times the
bottom frame-gradient cost. Expanding-plane stretching, strain mismatch,
and the parabolic off-diagonal source remain. No uniform budget is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorBudget

open scoped Topology ComplexConjugate RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open PancakeFrequencyProjectorCommutator PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open RankOneProjectorTangent BottomProjectorMotion LocalClusterAnisotropy LocalLowDiffusionBudget
open LocalBottomParabolicSectors LocalSpatialSpectralBounds LocalParabolicProjectorEquation
open LocalParabolicProjectorBound LocalBottomSectorBudget LocalWeightedSectorBalance LocalTopPlaneRate

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def dampingCoefficient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu theta : ℝ) (x : T3) : ℝ :=
  let g := bottomGap (spatialStrain modes (filteredVelocity chi u) x)
  g - 2 * nu * ((1 - theta) / theta) * strainGradientSquare chi modes u x / g ^ 2

def remainder (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu theta : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let K := parabolicCouplingEnvelope chi modes outputs u nu x
  mismatchWork chi modes u theta x +
    (2 * theta * topEigenvalue S + 3 * (1 - theta) ^ 2 * K ^ 2 / bottomGap S) *
      ‖expandingPlaneProjector S (fullVorticity u x)‖ ^ 2

theorem weighted_frameCross_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0)
    (hK : CouplingBound chi modes outputs u nu t x) :
    let S := spatialStrain modes (filteredVelocity chi (u t)) x
    (1 - theta) * frameCross chi modes u nu t x ≤
      (bottomGap S / 3) * LocalBottomEnergy.energy chi modes (u t) x +
        3 * (1 - theta) ^ 2 * parabolicCouplingEnvelope chi modes outputs (u t) nu x ^ 2 / bottomGap S *
          ‖expandingPlaneProjector S (fullVorticity (u t) x)‖ ^ 2 := by
  have h := Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion.abs_weighted_cross_le_young
    (bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x))
    (parabolicRate chi modes u nu t x)
    (lineProjector_mul_self _ (bottomVector_norm _))
    (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector _)).isSymmetric a b)
    (fun a b ↦ (parabolicRate_isSelfAdjoint chi modes u nu t x hg hP).isSymmetric a b)
    (fullVorticity (u t) x) (1 - theta)
    (parabolicCouplingEnvelope chi modes outputs (u t) nu x)
    (bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) / 3) hK (by positivity)
  have h' := (le_abs_self _).trans h
  change (1 - theta) * frameCross chi modes u nu t x ≤ _ at h'
  have hQ : expandingPlaneProjector (spatialStrain modes (filteredVelocity chi (u t)) x) =
      1 - bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x) := rfl
  dsimp only
  simp only [LocalBottomEnergy.energy, BottomProjectedEnergy.energy, hQ]
  convert! h' using 1
  ring

theorem planeStretch_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    planeStretch chi modes u x ≤ topEigenvalue S * ‖expandingPlaneProjector S (fullVorticity u x)‖ ^ 2 :=
  PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq _ _ _

theorem materialRate_add_damping_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (hnu : 0 ≤ nu)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hu : Summable (fourierMoment 3 (u t))) (hdiv : ∀ q, modeDot q (u t q) = 0) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0)
    (hK : CouplingBound chi modes outputs u nu t x) :
    LocalWeightedSectorEnergy.materialRate chi modes u nu theta t x -
        nu * LocalWeightedSectorEnergy.energyLaplacian chi modes (u t) theta x +
        2 * nu * dissipation chi modes (u t) theta x +
        dampingCoefficient chi modes (u t) nu theta x * LocalBottomEnergy.energy chi modes (u t) x ≤
      remainder chi modes outputs (u t) nu theta x := by
  have he := materialRate_sub_diffusion_add_dissipation_eq chi modes u nu theta t htheta.ne' hu x hg hP
  have hc := weighted_frameCross_le chi modes outputs u nu theta t x hg hP hK
  have hp := mul_le_mul_of_nonneg_left (planeStretch_le chi modes (u t) x)
    (show 0 ≤ 2 * theta by positivity)
  have hq : 0 ≤ (1 - theta) / theta := div_nonneg (sub_nonneg.mpr htheta1) htheta.le
  have hf := mul_le_mul_of_nonneg_left (bottomFrameGradientSquare_le chi modes (u t) x hg)
    (show 0 ≤ 2 * nu * ((1 - theta) / theta) by positivity)
  have hm := mul_le_mul_of_nonneg_right
    (FilteredStrainTrace.thirdEigenvalue_le_neg_two_thirds_bottomGap _
      (FilteredStrainTrace.trace_filteredStrain_eq_zero chi modes (u t) hdiv x))
    (BottomProjectedEnergy.energy_nonneg (spatialStrain modes (filteredVelocity chi (u t)) x)
      (fullVorticity (u t) x))
  change thirdEigenvalue _ * LocalBottomEnergy.energy chi modes (u t) x ≤
    -(2 / 3 : ℝ) * bottomGap _ * LocalBottomEnergy.energy chi modes (u t) x at hm
  unfold dampingCoefficient remainder
  dsimp only at hc hp hf ⊢
  simp only [div_eq_mul_inv] at he hc hf hm ⊢
  nlinarith only [he, hc, hp, hf, hm]

theorem half_gap_le_dampingCoefficient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu theta : ℝ) (htheta : 0 < theta) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x))
    (hsmall : 4 * nu * (1 - theta) * strainGradientSquare chi modes u x ≤
      theta * bottomGap (spatialStrain modes (filteredVelocity chi u) x) ^ 3) :
    bottomGap (spatialStrain modes (filteredVelocity chi u) x) / 2 ≤
      dampingCoefficient chi modes u nu theta x := by
  have hc : 2 * nu * ((1 - theta) / theta) * strainGradientSquare chi modes u x /
      bottomGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2 ≤
        bottomGap (spatialStrain modes (filteredVelocity chi u) x) / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hg)).mpr
    have hdiv : 4 * nu * (1 - theta) * strainGradientSquare chi modes u x / theta ≤
        bottomGap (spatialStrain modes (filteredVelocity chi u) x) ^ 3 :=
      (div_le_iff₀ htheta).mpr (by nlinarith only [hsmall])
    simp only [div_eq_mul_inv] at hdiv ⊢
    nlinarith only [hdiv]
  unfold dampingCoefficient
  linarith

/-- A bound for the actual frozen material derivative, not a freely supplied rate. -/
def Control (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (x : T3) : Prop :=
  HasDerivAt (fun h ↦ LocalWeightedSectorEnergy.frozenEnergy chi modes u theta t x h)
      (LocalWeightedSectorEnergy.materialRate chi modes u nu theta t x) 0 ∧
    deriv (fun h ↦ LocalWeightedSectorEnergy.frozenEnergy chi modes u theta t x h) 0 -
        nu * LocalWeightedSectorEnergy.energyLaplacian chi modes (u t) theta x +
        2 * nu * dissipation chi modes (u t) theta x +
        dampingCoefficient chi modes (u t) nu theta x * LocalBottomEnergy.energy chi modes (u t) x ≤
      remainder chi modes outputs (u t) nu theta x

theorem Control.half_gap_bound {chi : Wavevector → ℂ} {modes outputs : Finset Wavevector}
    {u : ℝ → FourierVelocity} {nu theta t : ℝ} {x : T3}
    (h : Control chi modes outputs u nu theta t x) (htheta : 0 < theta)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hsmall : 4 * nu * (1 - theta) * strainGradientSquare chi modes (u t) x ≤
      theta * bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) ^ 3) :
    deriv (fun h ↦ LocalWeightedSectorEnergy.frozenEnergy chi modes u theta t x h) 0 -
        nu * LocalWeightedSectorEnergy.energyLaplacian chi modes (u t) theta x +
        2 * nu * dissipation chi modes (u t) theta x +
        (bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x) / 2) * LocalBottomEnergy.energy chi modes (u t) x ≤
      remainder chi modes outputs (u t) nu theta x := by
  have hE : 0 ≤ LocalBottomEnergy.energy chi modes (u t) x := BottomProjectedEnergy.energy_nonneg _ _
  have hc := mul_le_mul_of_nonneg_right (half_gap_le_dampingCoefficient chi modes (u t) nu theta htheta x hg hsmall) hE
  have hb := h.2
  linarith only [hc, hb]

theorem ae_ae_control {nu T B : ℝ} {u₀ : FourierVelocity}
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
      ∀ theta : ℝ, 0 < theta → theta ≤ 1 → Control chi modes outputs s.coefficients nu theta t x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_differentiableAt_frozenProjectors s chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI,
    ae_ae_couplingBound s hnu chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI]
    with t ht hP hK
  have htm := Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t htm)
  filter_upwards [hP, hK] with x hp hk hgap theta htheta htheta1
  have hd := LocalWeightedSectorEnergy.hasDerivAt_frozenEnergy s g hg hSum hu chi modes theta
    a b hab hI t ht x (hp hgap).1
  refine ⟨hd, ?_⟩
  rw [hd.deriv]
  exact materialRate_add_damping_le chi modes outputs s.coefficients nu theta t hnu htheta htheta1 hm
    (s.transverse t) x hgap (hp hgap).1 (hk hgap)

theorem exists_physical_localWeightedSectorControl (nu : ℝ) (hnu : 0 < nu)
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
        ∀ theta : ℝ, 0 < theta → theta ≤ 1 → Control chi modes outputs s.coefficients nu theta t x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI
  exact ae_ae_control s hnu.le chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI g hg hSum hu

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorBudget
