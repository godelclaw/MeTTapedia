import Mettapedia.Analysis.PositiveOperatorKernelCurvature
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectControl
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyEnvelope

/-!
# Alignment-depleted cost of actual spectral diffusion

Top curvature pays the part of the mixed gradient carried by the top
eigenline. Positive constant regularization pays the remaining cross term
with the squared transverse vorticity, not its full norm. This local
simple-top estimate retains both its regularization cost and source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDiffusionDepletion

open scoped ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierStrainGradient
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakePhysicalLaplacian PancakePhysicalDiffusionLimit PancakeRegularizedDiffusion
open PancakeRegularizedMaterialRate PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open PancakeAnisotropyDepletion PancakeStrainSpectralFrame
open LocalSpatialSpectralRelation LocalSpatialTopEigenvalue LocalSpatialVorticityJets
open LocalLowDiffusionBudget LocalSpectralDefectDiffusion LocalSpectralDefectBalance
open LocalSpatialSpectralBounds

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def directionalCurvature (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
  eigenvalueSecond chi modes u j x - ⟪e, strainSecond modes (filteredVelocity chi u) j x e⟫

def misalignment (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  lineRemainder (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x)

theorem sum_directionalCurvature (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    ∑ j : Fin 3, directionalCurvature chi modes u j x = curvature chi modes u x := by
  simp only [directionalCurvature, curvature, eigenvalueLaplacian, strainLaplacian,
    sum_apply, inner_sum, Finset.sum_sub_distrib]

theorem kernel_curvature_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) (c : ℝ) (v : R3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    0 ≤ 2 * ⟪v, regularizedGap S 0 v⟫ + 4 * c * ⟪v, gapFirst chi modes u j x (topVector S)⟫ +
      c ^ 2 * directionalCurvature chi modes u j x := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  have he : S.1 (topVector S) = topEigenvalue S • topVector S :=
    (orderedEigenframe S.1 S.2).apply_eigenbasis 0
  have hk : regularizedGap (strainCurve chi modes u j x 0) 0 (c • topVector S) = 0 := by
    rw [strainCurve_zero]
    change regularizedGap S 0 (c • topVector S) = 0
    simp only [regularizedGap, add_zero, sub_apply, smul_apply, one_apply_eq_self, map_smul, he]
    module
  have h := Mettapedia.Analysis.PositiveOperatorKernelCurvature.second_order_form_nonneg
    (contDiffAt_gapCurve chi modes u 0 j x hg)
    (Filter.Eventually.of_forall (fun h a b ↦ (regularizedGap_symmetric
      (strainCurve chi modes u j x h) 0 a b).symm))
    (Filter.Eventually.of_forall (fun h w ↦ by
      simpa only [zero_mul] using regularizedGap_coercive (strainCurve chi modes u j x h) 0 w))
    (c • topVector S) v hk
  rw [deriv_deriv_gapCurve chi modes u 0 j x hg, deriv_gapCurve chi modes u 0 j x hg] at h
  simp only [strainCurve_zero, sub_apply, smul_apply, one_apply_eq_self,
    map_smul, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, topVector_norm] at h
  dsimp only [directionalCurvature]
  change 0 ≤ 2 * ⟪v, regularizedGap S 0 v⟫ + 4 * c * ⟪v, gapFirst chi modes u j x (topVector S)⟫ +
    c ^ 2 * (eigenvalueSecond chi modes u j x - ⟪topVector S, strainSecond modes (filteredVelocity chi u) j x (topVector S)⟫)
  nlinarith only [h]

theorem directionalProduction_depleted (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hd : 0 < delta) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) (w v : R3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let d := lineRemainder (topVector S) w;
    -directionalCurvature chi modes u j x * ‖w‖ ^ 2 - 2 * ⟪v, regularizedGap S delta v⟫ -
        4 * ⟪v, gapFirst chi modes u j x w⟫ + directionalCurvature chi modes u j x * ‖d‖ ^ 2 +
        delta * ‖v‖ ^ 2 ≤
      (16 / delta) * ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 * ‖d‖ ^ 2 := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  let c := ⟪topVector S, w⟫
  let d := lineRemainder (topVector S) w
  let G := gapFirst chi modes u j x
  have hk := kernel_curvature_nonneg chi modes u j x hg c v
  have hn : ‖d‖ ^ 2 = ‖w‖ ^ 2 - c ^ 2 := norm_lineRemainder_sq _ _ (topVector_norm S)
  have he : ⟪v, G w⟫ = c * ⟪v, G (topVector S)⟫ + ⟪v, G d⟫ := by
    simp only [d, lineRemainder, map_sub, map_smul, inner_sub_right, real_inner_smul_right, c]
    ring
  have ha : ⟪v, regularizedGap S delta v⟫ = ⟪v, regularizedGap S 0 v⟫ + delta * ‖v‖ ^ 2 := by
    simp only [regularizedGap_energy, zero_mul, add_zero]
  have hy := spectralDefect_forcing_young v ((-2 : ℝ) • G d) delta hd
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs] at hy
  norm_num at hy
  have hG := gapDerivative_norm S (strainGradient modes (filteredVelocity chi u) x j)
  have hop := G.le_opNorm d
  have hs : ‖G d‖ ^ 2 ≤ 4 * ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 * ‖d‖ ^ 2 := by
    calc
      _ ≤ (‖G‖ * ‖d‖) ^ 2 := by gcongr
      _ ≤ ((2 * ‖strainGradient modes (filteredVelocity chi u) x j‖) * ‖d‖) ^ 2 := by
        gcongr
        exact hG
      _ = _ := by ring
  have hp := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)) hd.le
  have hnc := congrArg (fun q : ℝ ↦ directionalCurvature chi modes u j x * q) hn
  dsimp only at hk ⊢
  change -directionalCurvature chi modes u j x * ‖w‖ ^ 2 - 2 * ⟪v, regularizedGap S delta v⟫ -
      4 * ⟪v, G w⟫ + directionalCurvature chi modes u j x * ‖d‖ ^ 2 + delta * ‖v‖ ^ 2 ≤ _
  rw [he, ha]
  simp only [div_eq_mul_inv] at hy hp ⊢
  nlinarith only [hk, hnc, hy, hp]

theorem gradientProduction_depleted (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hnu : 0 ≤ nu) (hd : 0 < delta) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    -nu * curvature chi modes u x * ‖fullVorticity u x‖ ^ 2 -
        2 * nu * gradientSquare chi modes u delta x - 4 * nu * gradientCross chi modes u x +
        nu * curvature chi modes u x * ‖misalignment chi modes u x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 ≤
      (16 * nu / delta) * strainGradientSquare chi modes u x * ‖misalignment chi modes u x‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun j _ ↦ directionalProduction_depleted chi modes u delta hd j x hg
      (fullVorticity u x) (fullCurlGradient u j x))
  have hn := mul_le_mul_of_nonneg_left h hnu
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_neg_distrib, sum_directionalCurvature] at hn
  change _ ≤ nu * ((16 / delta) * strainGradientSquare chi modes u x * ‖misalignment chi modes u x‖ ^ 2) at hn
  convert! hn using 1
  · simp only [gradientSquare, gradientCross, misalignment]
    ring
  · ring

theorem materialRate_sub_diffusion_depleted (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hnu : 0 ≤ nu) (hd : 0 < delta)
    (hu : Summable (fourierMoment 3 u)) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    materialRate chi modes outputs u nu delta x - nu * energyLaplacian chi modes u delta x +
        residualSquare chi modes u x + nu * curvature chi modes u x * ‖misalignment chi modes u x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 ≤
      nonviscousSource chi modes outputs u delta x +
        (16 * nu / delta) * strainGradientSquare chi modes u x * ‖misalignment chi modes u x‖ ^ 2 := by
  have he := materialRate_sub_diffusion_eq chi modes outputs u nu delta hu x hg
  have hp := gradientProduction_depleted chi modes u nu delta hnu hd x hg
  linarith only [he, hp]

theorem misalignment_sq_le_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hd : 0 < delta) (x : T3) :
    ‖misalignment chi modes u x‖ ^ 2 ≤
      energy chi modes u delta x / (topGap (spatialStrain modes (filteredVelocity chi u) x) + delta) := by
  apply (le_div_iff₀ (add_pos_of_nonneg_of_pos (topGap_nonneg _) hd)).mpr
  simpa only [misalignment, energy, LocalAlignmentTransport.alignmentEnergy, mul_comm] using
    SpectralAnisotropyEnvelope.regularizedGap_mul_lineRemainder_sq_le
    (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) delta hd.le

theorem misalignment_sq_le_defect (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ‖misalignment chi modes u x‖ ^ 2 ≤ energy chi modes u 0 x /
      topGap (spatialStrain modes (filteredVelocity chi u) x) := by
  rw [energy_zero]
  apply (le_div_iff₀ hg).mpr
  simpa only [misalignment, mul_comm] using SpectralAnisotropyEnvelope.topGap_mul_lineRemainder_sq_le
    (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

/-- No new derivative or summability assumption: the existing actual balance
supplies the material derivative, while curvature pays its aligned cross term. -/
theorem control_depleted_bound {chi : Wavevector → ℂ} {modes outputs : Finset Wavevector}
    {u : ℝ → FourierVelocity} {nu t : ℝ} {x : T3}
    (h : LocalSpectralDefectControl.Control chi modes outputs u nu t x) (hnu : 0 ≤ nu)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (delta : ℝ) (hd : 0 < delta) :
    deriv (fun h ↦ frozenEnergy chi modes u delta t x h) 0 -
        nu * energyLaplacian chi modes (u t) delta x + residualSquare chi modes (u t) x +
        nu * curvature chi modes (u t) x * ‖misalignment chi modes (u t) x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient (u t) j x‖ ^ 2 ≤
      nonviscousSource chi modes outputs (u t) delta x +
        (16 * nu / delta) * strainGradientSquare chi modes (u t) x * ‖misalignment chi modes (u t) x‖ ^ 2 := by
  have he := h.balance delta
  have hp := gradientProduction_depleted chi modes (u t) nu delta hnu hd x hg
  linarith only [he, hp]

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDiffusionDepletion
