import Mettapedia.Analysis.OrthogonalProjectionParabolic
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalParabolicProjectorBound

/-!
# Completed-square sector balance for actual bottom vorticity

The spatial and parabolic projector rates are proved self-adjoint. Their
signed sector identity exposes a favorable completed gradient square and
retains the complementary-gradient cross term. No payment of that term
over time or frequency scales is inferred.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomParabolicSectors

open scoped Topology ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeMaterialProjectorTangent
open RankOneProjectorTangent BottomProjectorMotion LocalClusterAnisotropy
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalBottomEnergy LocalAlignmentForcing
open LocalBottomEnergyDiffusion LocalSpatialSpectralBounds LocalParabolicProjectorEquation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem projectorSecond_isSelfAdjoint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    IsSelfAdjoint (projectorSecond chi modes u j x) := by
  have hP : ContDiffAt ℝ 2 (projectorCurve chi modes u j x) 0 :=
    (LocalSpatialBottomProjector.contDiffAt_projector_shift chi modes u x hg j).of_le (by decide)
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Mettapedia.Analysis.OperatorQuadraticForm.isSymmetric_second_derivative hP
    (Filter.Eventually.of_forall (fun h a b ↦
      (lineProjector_isSelfAdjoint (bottomVector (LocalSpatialSpectralRelation.strainCurve chi modes u j x h))).isSymmetric a b))

theorem projectorLaplacian_isSelfAdjoint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    IsSelfAdjoint (projectorLaplacian chi modes u x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro a b
  change ⟪projectorLaplacian chi modes u x a, b⟫ = ⟪a, projectorLaplacian chi modes u x b⟫
  simp only [projectorLaplacian, sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ (projectorSecond_isSelfAdjoint chi modes u j x hg).isSymmetric a b)

theorem parabolicRate_isSelfAdjoint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    IsSelfAdjoint (parabolicRate chi modes u nu t x) := by
  have hD := derivative_selfAdjoint _ _ 0 hP.hasDerivAt
    (fun h ↦ lineProjector_isSelfAdjoint (bottomVector (frozenStrain chi modes u t x h)))
  have hL := projectorLaplacian_isSelfAdjoint chi modes (u t) x hg
  rw [parabolicRate, neg_planeRate_eq_deriv_bottomProjector chi modes u t x hP]
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro a b
  change ⟪(deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0 -
      nu • projectorLaplacian chi modes (u t) x) a, b⟫ =
    ⟪a, (deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0 -
      nu • projectorLaplacian chi modes (u t) x) b⟫
  have hd : ⟪deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0 a, b⟫ =
      ⟪a, deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0 b⟫ := hD.isSymmetric a b
  have hl : ⟪projectorLaplacian chi modes (u t) x a, b⟫ =
      ⟪a, projectorLaplacian chi modes (u t) x b⟫ := hL.isSymmetric a b
  simp only [sub_apply, smul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hd, hl]

def bottomFrameGradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
  ∑ j : Fin 3, ‖projectorFirst chi modes u j x (P (fullVorticity u x))‖ ^ 2

def transverseGradientCross (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  ∑ j : Fin 3, ⟪expandingPlaneProjector S (fullCurlGradient u j x),
    projectorFirst chi modes u j x (bottomEigenlineProjector S (fullVorticity u x))⟫

def completedGradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  ∑ j : Fin 3, ‖bottomEigenlineProjector S (fullCurlGradient u j x) +
    projectorFirst chi modes u j x (expandingPlaneProjector S (fullVorticity u x))‖ ^ 2

def frameCross (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  let w := fullVorticity (u t) x
  2 * ⟪bottomEigenlineProjector S w, parabolicRate chi modes u nu t x (expandingPlaneProjector S w)⟫

def sectorSource (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  2 * ⟪bottomEigenlineProjector S (fullVorticity (u t) x), strainMismatch chi modes (u t) x⟫ +
    frameCross chi modes u nu t x + 2 * nu * bottomFrameGradientSquare chi modes (u t) x -
      4 * nu * transverseGradientCross chi modes (u t) x

theorem completedGradientSquare_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ completedGradientSquare chi modes u x :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem bottomFrameGradientSquare_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    bottomFrameGradientSquare chi modes u x ≤
      strainGradientSquare chi modes u x / bottomGap S ^ 2 * energy chi modes u x := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  let a := bottomEigenlineProjector S (fullVorticity u x)
  calc
    _ ≤ ∑ j : Fin 3,
        (‖PancakeFourierStrainGradient.strainGradient modes (filteredVelocity chi u) x j‖ / bottomGap S * ‖a‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_projectorFirst_apply_bottomProjector_le chi modes u j x hg _) 2
    _ = _ := by
      simp only [strainGradientSquare, energy, BottomProjectedEnergy.energy, Fin.sum_univ_three, S, a]
      ring

theorem abs_frameCross_le_young (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0)
    (K rho : ℝ) (hrho : 0 < rho)
    (hK : ‖bottomCoupling (spatialStrain modes (filteredVelocity chi (u t)) x)
      (parabolicRate chi modes u nu t x)‖ ≤ K) :
    |frameCross chi modes u nu t x| ≤ rho * energy chi modes (u t) x +
      K ^ 2 / rho * ‖expandingPlaneProjector
        (spatialStrain modes (filteredVelocity chi (u t)) x) (fullVorticity (u t) x)‖ ^ 2 := by
  exact Mettapedia.Analysis.OrthogonalProjectionParabolic.abs_cross_le_young _ _
    (lineProjector_mul_self _ (bottomVector_norm (spatialStrain modes (filteredVelocity chi (u t)) x)))
    (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector (spatialStrain modes (filteredVelocity chi (u t)) x))).isSymmetric a b)
    (fun a b ↦ (parabolicRate_isSelfAdjoint chi modes u nu t x hg hP).isSymmetric a b)
    _ K rho hK hrho

theorem signed_diffusion_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    let w := fullVorticity (u t) x
    ⟪w, parabolicRate chi modes u nu t x w⟫ - 2 * nu * projectedGradientSquare chi modes (u t) x -
        4 * nu * gradientCrossTerm chi modes (u t) x =
      frameCross chi modes u nu t x + 2 * nu * bottomFrameGradientSquare chi modes (u t) x -
        4 * nu * transverseGradientCross chi modes (u t) x - 2 * nu * completedGradientSquare chi modes (u t) x := by
  exact Mettapedia.Analysis.OrthogonalProjectionParabolic.signed_diffusion_split _ _ _ nu
    (lineProjector_mul_self _ (bottomVector_norm (spatialStrain modes (filteredVelocity chi (u t)) x)))
    (fun a b ↦ (lineProjector_isSelfAdjoint (bottomVector (spatialStrain modes (filteredVelocity chi (u t)) x))).isSymmetric a b)
    (fun a b ↦ (parabolicRate_isSelfAdjoint chi modes u nu t x hg hP).isSymmetric a b)
    (fun j a b ↦ (projectorFirst_isSelfAdjoint chi modes (u t) j x hg).isSymmetric a b)
    (fun j ↦ projectorFirst_tangent chi modes (u t) j x hg)
    (parabolicRate_constraint chi modes u nu t x hg hP) _ _

theorem materialRate_sub_diffusion_add_completedSquare_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hu : Summable (fourierMoment 3 (u t))) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    LocalBottomEnergy.materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x +
      2 * nu * completedGradientSquare chi modes (u t) x =
      2 * thirdEigenvalue (spatialStrain modes (filteredVelocity chi (u t)) x) * energy chi modes (u t) x +
        sectorSource chi modes u nu t x := by
  have hs := signed_diffusion_split chi modes u nu t x hg hP
  have he := materialRate_sub_diffusion_eq chi modes u nu t hu x hg
  dsimp only at hs he ⊢
  unfold sectorSource
  change _ = _ at he
  dsimp only at he ⊢
  unfold parabolicRate at hs
  linarith

theorem materialRate_sub_diffusion_add_damping_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (hnu : 0 ≤ nu) (hu : Summable (fourierMoment 3 (u t)))
    (hdiv : ∀ q, modeDot q (u t q) = 0) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0)
    (K rho : ℝ) (hrho : 0 < rho)
    (hK : ‖bottomCoupling (spatialStrain modes (filteredVelocity chi (u t)) x)
      (parabolicRate chi modes u nu t x)‖ ≤ K) :
    let S := spatialStrain modes (filteredVelocity chi (u t)) x
    LocalBottomEnergy.materialRate chi modes u nu t x - nu * energyLaplacian chi modes (u t) x +
        2 * nu * completedGradientSquare chi modes (u t) x +
        ((4 / 3 : ℝ) * bottomGap S - 2 * nu * strainGradientSquare chi modes (u t) x / bottomGap S ^ 2 - rho) *
          energy chi modes (u t) x ≤
      2 * ⟪bottomEigenlineProjector S (fullVorticity (u t) x), strainMismatch chi modes (u t) x⟫ +
        K ^ 2 / rho * ‖expandingPlaneProjector S (fullVorticity (u t) x)‖ ^ 2 -
        4 * nu * transverseGradientCross chi modes (u t) x := by
  have he := materialRate_sub_diffusion_add_completedSquare_eq chi modes u nu t hu x hg hP
  have hf := bottomFrameGradientSquare_le chi modes (u t) x hg
  have hc := (le_abs_self _).trans (abs_frameCross_le_young chi modes u nu t x hg hP K rho hrho hK)
  have hmu := FilteredStrainTrace.thirdEigenvalue_le_neg_two_thirds_bottomGap _
    (FilteredStrainTrace.trace_filteredStrain_eq_zero chi modes (u t) hdiv x)
  have hE := BottomProjectedEnergy.energy_nonneg (spatialStrain modes (filteredVelocity chi (u t)) x)
    (fullVorticity (u t) x)
  change 0 ≤ energy chi modes (u t) x at hE
  have hmuE := mul_le_mul_of_nonneg_right hmu hE
  have hnf := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * nu by positivity)
  dsimp only at hnf ⊢
  unfold sectorSource at he
  dsimp only at he
  simp only [div_eq_mul_inv] at hc hnf hmuE ⊢
  nlinarith only [he, hc, hnf, hmuE]

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomParabolicSectors
