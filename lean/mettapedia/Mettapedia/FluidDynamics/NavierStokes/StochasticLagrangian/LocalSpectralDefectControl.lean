import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity

/-!
# Spectral-defect diffusion control constructed from physical data

One local infinite Fourier solution supplies the exact parabolic identity
for every admissible finite filter and every constant regularization. It
holds pointwise on the positive-top-gap branch. The positive-regularization
bound retains its actual strain-gradient cost and nonviscous source.
This is local control, not a frequency-uniform global continuation bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectControl

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFrequencyProjectorCommutator
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks PancakeHigherLocalVelocity
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalSpatialTopEigenvalue LocalSpatialVorticityJets LocalLowDiffusionBudget
open LocalSpectralDefectDiffusion LocalSpectralDefectBalance LocalSpatialSpectralBounds

local notation "T3" => UnitAddTorus (Fin 3)

/-- All rates are derivatives of the constructed field energy. -/
structure Control (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : Prop where
  curvature_nonneg : 0 ≤ curvature chi modes (u t) x
  differentiable (delta : ℝ) :
    HasDerivAt (fun h ↦ frozenEnergy chi modes u delta t x h)
      (materialRate chi modes outputs (u t) nu delta x) 0
  balance (delta : ℝ) :
    deriv (fun h ↦ frozenEnergy chi modes u delta t x h) 0 -
        nu * energyLaplacian chi modes (u t) delta x + residualSquare chi modes (u t) x +
        nu * curvature chi modes (u t) x * ‖fullVorticity (u t) x‖ ^ 2 +
        2 * nu * gradientSquare chi modes (u t) delta x =
      nonviscousSource chi modes outputs (u t) delta x - 4 * nu * gradientCross chi modes (u t) x
  paid (delta : ℝ) (hd : 0 < delta) :
    deriv (fun h ↦ frozenEnergy chi modes u delta t x h) 0 -
        nu * energyLaplacian chi modes (u t) delta x + residualSquare chi modes (u t) x +
        nu * curvature chi modes (u t) x * ‖fullVorticity (u t) x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient (u t) j x‖ ^ 2 ≤
      nonviscousSource chi modes outputs (u t) delta x +
        (16 * nu / delta) * strainGradientSquare chi modes (u t) x * ‖fullVorticity (u t) x‖ ^ 2

theorem control {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (hgap : 0 < topGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) :
    Control chi modes outputs s.coefficients nu t x := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  have hd := hasDerivAt_frozenEnergy s chi C hchi modes outputs hcut hchir hsub hout hs hk
    g hg hSum hu a b hab hI
  refine ⟨LocalSpatialTopEigenvalue.curvature_nonneg chi modes (s.coefficients t) x hgap,
    (fun delta ↦ hd delta t ht x hgap), ?_, ?_⟩
  · intro delta
    rw [(hd delta t ht x hgap).deriv]
    exact materialRate_sub_diffusion_eq chi modes outputs (s.coefficients t) nu delta hm x hgap
  · intro delta hdelta
    rw [(hd delta t ht x hgap).deriv]
    exact materialRate_sub_diffusion_le chi modes outputs (s.coefficients t) nu delta hnu hdelta hm x hgap

theorem exists_physical_localSpectralDefectControl (nu : ℝ) (hnu : 0 < nu)
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
      ∀ t ∈ Set.Ioo a b, ∀ x : T3,
        0 < topGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
        Control chi modes outputs s.coefficients nu t x := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI t ht x hgap
  exact control s hnu.le chi C hchi modes outputs hcut hchir hsub hout hs hk
    g hg hSum hu a b hab hI t ht x hgap

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectControl
