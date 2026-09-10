import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralRelation

/-!
# Bottom-gap bounds for actual spatial projector gradients

The scalar eigenvalue derivative and the transverse projector derivative
are controlled by the actual strain gradient. The mixed source requires
one inverse bottom gap, not a bound on the strain Laplacian. No estimate
uniform through bottom-gap closure is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpatialSpectralBounds

open scoped Topology ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeFourierStrainGradient PancakeMaterialProjectorTangent PancakeEigenframePerturbation
open RankOneProjectorTangent BottomProjectorMotion LocalBottomEnergyDiffusion
open LocalSpatialSpectralRelation LocalSpatialBottomProjector SpectralClusterAnisotropy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem hasDerivAt_projectorCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    HasDerivAt (projectorCurve chi modes u j x) (projectorFirst chi modes u j x) 0 :=
  ((contDiffAt_projector_shift chi modes u x hg j).differentiableAt (by simp)).hasDerivAt

theorem projectorFirst_tangent (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    projectorFirst chi modes u j x * P + P * projectorFirst chi modes u j x = projectorFirst chi modes u j x := by
  have h := derivative_projector_tangent _ _ 0 (hasDerivAt_projectorCurve chi modes u j x hg)
    (fun h ↦ lineProjector_mul_self _ (bottomVector_norm (strainCurve chi modes u j x h)))
  simpa only [projectorCurve, coordinateShift_zero, add_zero] using h

theorem projectorFirst_isSelfAdjoint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    IsSelfAdjoint (projectorFirst chi modes u j x) :=
  derivative_selfAdjoint _ _ 0 (hasDerivAt_projectorCurve chi modes u j x hg)
    (fun h ↦ lineProjector_isSelfAdjoint (bottomVector (strainCurve chi modes u j x h)))

theorem abs_bottomEigenvalueFirst_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    |bottomEigenvalueFirst chi modes u j x| ≤ ‖strainGradient modes (filteredVelocity chi u) x j‖ := by
  have hmc := contDiffAt_bottomEigenvalueCurve (n := 1) chi modes u j x (by norm_num) hg
  have hm := (hmc.differentiableAt (by norm_num)).hasDerivAt
  have he := StrainEigenvalueRates.thirdEigenvalue_derivative_eq_of_hasDerivAt
    (strainCurve chi modes u j x) _ _ 0 (hasDerivAt_strainCurve chi modes u j x 0) hm
    (bottomVector (strainCurve chi modes u j x 0)) (bottomVector_norm _)
    (apply_bottomVector _)
  simp only [strainCurve_zero, coordinateShift_zero, add_zero] at he
  change bottomEigenvalueFirst chi modes u j x = _ at he
  rw [he]
  calc
    _ ≤ ‖bottomVector (spatialStrain modes (filteredVelocity chi u) x)‖ *
        ‖strainGradient modes (filteredVelocity chi u) x j (bottomVector (spatialStrain modes (filteredVelocity chi u) x))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ _ := by
      rw [bottomVector_norm, one_mul]
      simpa only [bottomVector_norm, mul_one] using
        (strainGradient modes (filteredVelocity chi u) x j).le_opNorm
          (bottomVector (spatialStrain modes (filteredVelocity chi u) x))

theorem norm_projectorFirst_apply_bottom_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    ‖projectorFirst chi modes u j x (bottomVector S)‖ ≤
      ‖strainGradient modes (filteredVelocity chi u) x j‖ / bottomGap S := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  let SG := strainGradient modes (filteredVelocity chi u) x j
  have hmc := contDiffAt_bottomEigenvalueCurve (n := 1) chi modes u j x (by norm_num) hg
  have hm := (hmc.differentiableAt (by norm_num)).hasDerivAt
  have he := bottomProjector_derivative_equation (strainCurve chi modes u j x) _ _ _ 0
    (hasDerivAt_strainCurve chi modes u j x 0) (hasDerivAt_projectorCurve chi modes u j x hg) hm
  simp only [strainCurve_zero, coordinateShift_zero, add_zero] at he
  have he' : (-S.1 * S.1 + (SG + S.1 * S.1)) * bottomEigenlineProjector S +
      S.1 * projectorFirst chi modes u j x =
      bottomEigenvalueFirst chi modes u j x • bottomEigenlineProjector S +
        thirdEigenvalue S • projectorFirst chi modes u j x := by
    rw [show -S.1 * S.1 + (SG + S.1 * S.1) = SG by
      apply ContinuousLinearMap.ext
      intro w
      simp only [add_apply, mul_apply_eq_comp, neg_apply]
      abel]
    exact he
  have hc := norm_bottomProjector_tangent_apply_le S (SG + S.1 * S.1) _ _ hg
    (projectorFirst_tangent chi modes u j x hg) he'
  have hz : (S.1 * S.1) (bottomVector S) = thirdEigenvalue S ^ 2 • bottomVector S := by
    simp only [mul_apply_eq_comp, apply_bottomVector, map_smul, smul_smul, pow_two]
  rw [bottomCoupling_add_preserving S SG (S.1 * S.1) _ hz] at hc
  exact hc.trans (div_le_div_of_nonneg_right (norm_bottomCoupling_le S SG) hg.le)

theorem norm_projectorFirst_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    ‖projectorFirst chi modes u j x‖ ≤
      2 * ‖strainGradient modes (filteredVelocity chi u) x j‖ / bottomGap S := by
  have h := norm_tangent_le_two_mul _ (bottomVector_norm (spatialStrain modes (filteredVelocity chi u) x))
    (projectorFirst chi modes u j x) (projectorFirst_isSelfAdjoint chi modes u j x hg)
    (projectorFirst_tangent chi modes u j x hg)
  calc
    _ ≤ _ := h
    _ ≤ 2 * (‖strainGradient modes (filteredVelocity chi u) x j‖ /
        bottomGap (spatialStrain modes (filteredVelocity chi u) x)) := by
      gcongr
      exact norm_projectorFirst_apply_bottom_le chi modes u j x hg
    _ = _ := by ring

def strainGradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2

theorem strainGradientSquare_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ strainGradientSquare chi modes u x :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem norm_bottomCoupling_mixedGradient_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    ‖bottomCoupling S (mixedGradient chi modes u x)‖ ≤
      2 * strainGradientSquare chi modes u x / bottomGap S := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  dsimp only
  rw [norm_bottomCoupling]
  calc
    _ ≤ ‖mixedGradient chi modes u x (bottomVector S)‖ :=
      norm_expandingPlaneProjector_apply_le S _
    _ ≤ ∑ j : Fin 3, ‖(strainGradient modes (filteredVelocity chi u) x j * projectorFirst chi modes u j x -
        bottomEigenvalueFirst chi modes u j x • projectorFirst chi modes u j x) (bottomVector S)‖ := by
      simp only [mixedGradient, sum_apply]
      exact norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, 2 * ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 / bottomGap S := by
      apply Finset.sum_le_sum
      intro j _
      let a := ‖strainGradient modes (filteredVelocity chi u) x j‖
      let v := projectorFirst chi modes u j x (bottomVector S)
      calc
        _ ≤ ‖strainGradient modes (filteredVelocity chi u) x j v‖ +
            ‖bottomEigenvalueFirst chi modes u j x • v‖ := norm_sub_le _ _
        _ ≤ a * ‖v‖ + |bottomEigenvalueFirst chi modes u j x| * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (strainGradient modes (filteredVelocity chi u) x j).le_opNorm v
        _ ≤ a * ‖v‖ + a * ‖v‖ := by
          gcongr
          exact abs_bottomEigenvalueFirst_le chi modes u j x hg
        _ = 2 * a * ‖v‖ := by ring
        _ ≤ 2 * a * (a / bottomGap S) := by
          gcongr
          exact norm_projectorFirst_apply_bottom_le chi modes u j x hg
        _ = _ := by ring
    _ = _ := by simp only [strainGradientSquare, Fin.sum_univ_three, S]; ring

end Mettapedia.FluidDynamics.NavierStokes.LocalSpatialSpectralBounds
