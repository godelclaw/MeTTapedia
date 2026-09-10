import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedSectorEnergy

/-!
# Coupled-sector diffusion with explicit inverse-weight cost

Both vorticity-gradient cross terms are completed against the weighted
sector dissipation. The expanding-plane stretching and frame-motion source
remain explicit; the identity is not a global regularity estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorBalance

open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain LocalClusterAnisotropy
open RankOneProjectorTangent BottomProjectorMotion BottomParabolicProjectorMotion
open LocalBottomEnergyDiffusion LocalBottomParabolicSectors LocalSpatialSpectralBounds
open LocalParabolicProjectorEquation LocalLowDiffusionBudget LocalSpatialVorticityJets LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def dissipation (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let P := bottomEigenlineProjector S
  let Q := expandingPlaneProjector S
  let w := fullVorticity u x
  (∑ j : Fin 3, ‖P (fullCurlGradient u j x) + (1 - theta) • projectorFirst chi modes u j x (Q w)‖ ^ 2) +
    theta * (∑ j : Fin 3, ‖Q (fullCurlGradient u j x) + ((1 - theta) / theta) • projectorFirst chi modes u j x (P w)‖ ^ 2) +
    theta * (1 - theta) * (∑ j : Fin 3, ‖projectorFirst chi modes u j x (Q w)‖ ^ 2)

def mismatchWork (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := fullVorticity u x
  2 * ⟪bottomEigenlineProjector S w + theta • expandingPlaneProjector S w, strainMismatch chi modes u x⟫

def planeStretch (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let b := expandingPlaneProjector S (fullVorticity u x)
  ⟪b, S.1 b⟫

theorem dissipation_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (x : T3) :
    0 ≤ dissipation chi modes u theta x := by
  unfold dissipation
  exact add_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    (mul_nonneg htheta (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))))
    (mul_nonneg (mul_nonneg htheta (sub_nonneg.mpr htheta1)) (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

theorem dissipation_one (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : dissipation chi modes u 1 x = LocalEnstrophyDiffusion.gradientSquare u x := by
  simp only [dissipation, sub_self, zero_div, zero_smul, add_zero, one_mul, mul_zero, zero_mul]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun j _ ↦
    Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion.norm_sq_eq_add
      (bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x))
      (lineProjector_mul_self _ (bottomVector_norm _))
      (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector _)).isSymmetric a b) (fullCurlGradient u j x))
  have hQ : expandingPlaneProjector (spatialStrain modes (filteredVelocity chi u) x) =
      1 - bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x) := rfl
  simp only [hQ]
  simpa only [Finset.sum_add_distrib, LocalEnstrophyDiffusion.gradientSquare] using h.symm

theorem strainWork_split (S : SymmetricStrain) (w : R3) :
    ⟪w, S.1 w⟫ = thirdEigenvalue S * BottomProjectedEnergy.energy S w +
      ⟪expandingPlaneProjector S w, S.1 (expandingPlaneProjector S w)⟫ := by
  have hq := inner_strain_plane_eq S (expandingPlaneProjector S w) w (inner_bottom_plane_eq_zero S w)
  have hp := BottomProjectedEnergy.inner_bottomProjector_strain S w
  calc
    _ = ⟪bottomEigenlineProjector S w, S.1 w⟫ + ⟪expandingPlaneProjector S w, S.1 w⟫ := by
      change _ = _ + ⟪w - bottomEigenlineProjector S w, S.1 w⟫
      rw [inner_sub_left]
      ring
    _ = _ := by rw [hp, ← hq]

theorem fullStrainWork_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let w := fullVorticity u x
    ⟪w, fullStrainOperator u x w⟫ = thirdEigenvalue S * LocalBottomEnergy.energy chi modes u x +
      planeStretch chi modes u x + ⟪w, strainMismatch chi modes u x⟫ := by
  have h := strainWork_split (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)
  simp only [strainMismatch, sub_apply, inner_sub_right, planeStretch, LocalBottomEnergy.energy]
  linarith

theorem mismatchWork_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (theta : ℝ) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let w := fullVorticity u x
    mismatchWork chi modes u theta x = (1 - theta) * (2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes u x⟫) +
      theta * (2 * ⟪w, strainMismatch chi modes u x⟫) := by
  unfold mismatchWork
  change 2 * ⟪_ + theta • (fullVorticity u x - bottomEigenlineProjector _ (fullVorticity u x)), _⟫ = _
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

theorem weighted_diffusion_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (htheta : theta ≠ 0) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    let w := fullVorticity (u t) x
    (1 - theta) * (⟪w, parabolicRate chi modes u nu t x w⟫ -
        2 * nu * projectedGradientSquare chi modes (u t) x - 4 * nu * gradientCrossTerm chi modes (u t) x) -
        2 * nu * theta * LocalEnstrophyDiffusion.gradientSquare (u t) x =
      (1 - theta) * frameCross chi modes u nu t x +
        2 * nu * ((1 - theta) / theta) * bottomFrameGradientSquare chi modes (u t) x -
        2 * nu * dissipation chi modes (u t) theta x := by
  have h := Mettapedia.Analysis.OrthogonalProjectionWeightedDiffusion.weighted_signed_diffusion_split
    (bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x))
    (parabolicRate chi modes u nu t x) (fun j ↦ projectorFirst chi modes (u t) j x) nu theta htheta
    (lineProjector_mul_self _ (bottomVector_norm _))
    (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector _)).isSymmetric a b)
    (fun a b ↦ (parabolicRate_isSelfAdjoint chi modes u nu t x hg hP).isSymmetric a b)
    (fun j a b ↦ (projectorFirst_isSelfAdjoint chi modes (u t) j x hg).isSymmetric a b)
    (fun j ↦ projectorFirst_tangent chi modes (u t) j x hg)
    (parabolicRate_constraint chi modes u nu t x hg hP) (fullVorticity (u t) x) (fun j ↦ fullCurlGradient (u t) j x)
  dsimp only at h ⊢
  unfold projectedGradientSquare gradientCrossTerm LocalEnstrophyDiffusion.gradientSquare
    frameCross bottomFrameGradientSquare dissipation
  dsimp only
  have hQ : expandingPlaneProjector (spatialStrain modes (filteredVelocity chi (u t)) x) =
      1 - bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x) := rfl
  simp only [hQ]
  convert! h using 1
  ring

theorem materialRate_sub_diffusion_add_dissipation_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu theta t : ℝ) (htheta : theta ≠ 0)
    (hu : Summable (fourierMoment 3 (u t))) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    LocalWeightedSectorEnergy.materialRate chi modes u nu theta t x -
        nu * LocalWeightedSectorEnergy.energyLaplacian chi modes (u t) theta x +
        2 * nu * dissipation chi modes (u t) theta x =
      2 * thirdEigenvalue (spatialStrain modes (filteredVelocity chi (u t)) x) * LocalBottomEnergy.energy chi modes (u t) x +
        2 * theta * planeStretch chi modes (u t) x + mismatchWork chi modes (u t) theta x +
        (1 - theta) * frameCross chi modes u nu t x +
        2 * nu * ((1 - theta) / theta) * bottomFrameGradientSquare chi modes (u t) x := by
  rw [LocalWeightedSectorEnergy.energyLaplacian_eq chi modes (u t) hu theta x hg, mismatchWork_eq]
  unfold LocalWeightedSectorEnergy.materialRate
  have hb := LocalBottomEnergyDiffusion.materialRate_sub_diffusion_eq chi modes u nu t hu x hg
  have hf := LocalEnstrophyDiffusion.materialRate_sub_diffusion_add_gradient_eq (u t) nu hu x
  have hd := weighted_diffusion_split chi modes u nu theta t htheta x hg hP
  have hs := fullStrainWork_split chi modes (u t) x
  dsimp only at hb hd hs ⊢
  unfold parabolicRate at hd
  linear_combination (1 - theta) * hb + theta * hf + hd + 2 * theta * hs

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedSectorBalance
