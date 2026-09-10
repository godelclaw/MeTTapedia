import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFrozenVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralBounds

/-!
# Principal viscous cancellation for the actual spectral defect

The strain Laplacian and vorticity Laplacian cancel against the actual
energy Laplacian. The remaining spectral curvature has the dissipative
sign. Mixed gradients are paid only for positive constant regularization;
the regularization's stretching and the nonviscous remainder stay explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectBalance

open scoped ContDiff RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFourierStrainGradient
open PancakeFrequencyProjectorCommutator
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakePhysicalLaplacian PancakeRegularizedDiffusion PancakeRegularizedMaterialRate
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open LocalSpatialTopEigenvalue LocalSpatialVorticityJets LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalClusterAnisotropy LocalFrozenVorticity LocalAlignmentForcing
open LocalSpectralDefectDiffusion LocalSpatialSpectralBounds

local notation "T3" => UnitAddTorus (Fin 3)

def frozenEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  regularizedEnergy (frozenStrain chi modes u t x h) delta (frozenVorticity u t x h)

/-- Reuse the existing full-field rate, with viscosity preceding regularization. -/
abbrev materialRate (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (x : T3) : ℝ :=
  LocalAlignmentForcing.materialRate chi modes outputs u delta nu x

def residualSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ‖LocalAlignmentForcing.residual chi modes u x‖ ^ 2

def nonviscousSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  remainderAnisotropy (nonviscousRemainder chi modes outputs u x) (topVector S) (fullVorticity u x) +
    2 * ⟪spectralResidual S.1 (topEigenvalue S) (fullVorticity u x), strainMismatch chi modes u x⟫ +
    2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem materialRate_viscous_split (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    materialRate chi modes outputs u nu delta x = -residualSquare chi modes u x +
      nonviscousSource chi modes outputs u delta x +
      nu * linearRate S delta (fullVorticity u x)
        (strainLaplacian modes (filteredVelocity chi u) x) (fullVorticityLaplacian u x) := by
  rw [materialRate, LocalAlignmentForcing.materialRate, linearRate_viscous_split]
  simp only [residualSquare, LocalAlignmentForcing.residual, nonviscousSource,
    strainMismatch, sub_apply, add_sub_cancel]
  ring

theorem materialRate_sub_diffusion_eq (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hu : Summable (fourierMoment 3 u)) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    materialRate chi modes outputs u nu delta x - nu * energyLaplacian chi modes u delta x +
        residualSquare chi modes u x + nu * curvature chi modes u x * ‖fullVorticity u x‖ ^ 2 +
        2 * nu * gradientSquare chi modes u delta x =
      nonviscousSource chi modes outputs u delta x - 4 * nu * gradientCross chi modes u x := by
  rw [materialRate_viscous_split, energyLaplacian_eq chi modes u delta hu x hg]
  ring

theorem gradientProduction_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hnu : 0 ≤ nu) (hd : 0 < delta) (x : T3) :
    -2 * nu * gradientSquare chi modes u delta x - 4 * nu * gradientCross chi modes u x +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 ≤
      (16 * nu / delta) * strainGradientSquare chi modes u x * ‖fullVorticity u x‖ ^ 2 := by
  have h := gradientProduction_sum_paid (Finset.univ : Finset (Fin 3))
    (spatialStrain modes (filteredVelocity chi u) x) delta nu
    (strainGradient modes (filteredVelocity chi u) x) (fullVorticity u x)
    (fun j ↦ fullCurlGradient u j x) hd hnu
  simp only [gradientProduction, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at h
  change _ ≤ (16 * nu / delta) * strainGradientSquare chi modes u x * ‖fullVorticity u x‖ ^ 2 at h
  convert! h using 1
  simp only [gradientSquare, gradientCross, gapFirst]
  ring

theorem materialRate_sub_diffusion_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hnu : 0 ≤ nu) (hd : 0 < delta)
    (hu : Summable (fourierMoment 3 u)) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    materialRate chi modes outputs u nu delta x - nu * energyLaplacian chi modes u delta x +
        residualSquare chi modes u x + nu * curvature chi modes u x * ‖fullVorticity u x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 ≤
      nonviscousSource chi modes outputs u delta x +
        (16 * nu / delta) * strainGradientSquare chi modes u x * ‖fullVorticity u x‖ ^ 2 := by
  have he := materialRate_sub_diffusion_eq chi modes outputs u nu delta hu x hg
  have hp := gradientProduction_le chi modes u nu delta hnu hd x
  linarith only [he, hp]

theorem hasDerivAt_frozenEnergy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (delta t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (hgap : 0 < topGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) :
    HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients delta t x h)
      (materialRate chi modes outputs (s.coefficients t) nu delta x) 0 := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk
    t (hI (Set.Ioo_subset_Icc_self ht)) x
  have hw := hasDerivAt_frozenVorticity s g hg hSum hu a b hab hI t ht x
  have hl := PancakeTopEigenvalueDerivative.hasDerivAt_topEigenvalue
    (frozenStrain chi modes s.coefficients t x) _ 0 hS
    (by simpa only [frozenStrain_zero] using hgap)
  have h := hasDerivAt_regularizedEnergy (frozenStrain chi modes s.coefficients t x)
    (frozenVorticity s.coefficients t x) _ _ delta 0 hS hw hl.differentiableAt
  change HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients delta t x h) _ 0 at h
  apply h.congr_deriv
  simp only [materialRate, LocalAlignmentForcing.materialRate, frozenStrain_zero, frozenVorticity_zero, jointRemainder,
    strainMismatch, sub_apply, add_sub_cancel, add_assoc]

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectBalance
