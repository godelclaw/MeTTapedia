import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomProjectorMotion

/-!
# Transverse coercivity without a tangent hypothesis

A material-minus-diffusion projector rate need not be tangent. Its
bottom-to-plane block is nevertheless controlled directly by the
spectral equation. The diagonal defect never needs to be discarded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BottomParabolicProjectorMotion

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeEigenframePerturbation
open RankOneProjectorTangent BottomProjectorMotion

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem inner_bottom_plane_eq_zero (S : SymmetricStrain) (w : R3) :
    ⟪bottomVector S, expandingPlaneProjector S w⟫ = 0 := by
  change ⟪bottomVector S, w - ⟪bottomVector S, w⟫ • bottomVector S⟫ = 0
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, bottomVector_norm]
  ring

theorem inner_plane_eq (S : SymmetricStrain) (v w : R3) (hv : ⟪bottomVector S, v⟫ = 0) :
    ⟪v, expandingPlaneProjector S w⟫ = ⟪v, w⟫ := by
  have hz : ⟪v, bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  change ⟪v, w - ⟪bottomVector S, w⟫ • bottomVector S⟫ = ⟪v, w⟫
  rw [inner_sub_right, real_inner_smul_right, hz, mul_zero, sub_zero]

theorem inner_strain_plane_eq (S : SymmetricStrain) (v w : R3)
    (hv : ⟪bottomVector S, v⟫ = 0) :
    ⟪v, S.1 (expandingPlaneProjector S w)⟫ = ⟪v, S.1 w⟫ := by
  have hz : ⟪v, bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  change ⟪v, S.1 (w - ⟪bottomVector S, w⟫ • bottomVector S)⟫ = ⟪v, S.1 w⟫
  rw [map_sub, map_smul, apply_bottomVector, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, hz, mul_zero, mul_zero, sub_zero]

/-- Only the off-diagonal block is estimated. `W` need not satisfy the
first-order projector tangent identity, nor be self-adjoint. -/
theorem norm_bottomCoupling_le_of_spectral_relation (S : SymmetricStrain) (R W F : Op)
    (sigma : ℝ) (hg : 0 < bottomGap S)
    (heq : (-S.1 * S.1 + R) * bottomEigenlineProjector S + S.1 * W =
      sigma • bottomEigenlineProjector S + thirdEigenvalue S • W + F) :
    ‖bottomCoupling S W‖ ≤ ‖bottomCoupling S (R - F)‖ / bottomGap S := by
  let v := expandingPlaneProjector S (W (bottomVector S))
  have hv : ⟪bottomVector S, v⟫ = 0 := inner_bottom_plane_eq_zero S _
  have hp : bottomEigenlineProjector S (bottomVector S) = bottomVector S :=
    lineProjector_apply_self _ (bottomVector_norm S)
  have hz : ⟪v, bottomVector S⟫ = 0 := by rw [real_inner_comm]; exact hv
  have hi : ⟪v, W (bottomVector S)⟫ = ‖v‖ ^ 2 := by
    rw [← inner_plane_eq S v _ hv, real_inner_self_eq_norm_sq]
  have he := congrArg (fun A : Op ↦ ⟪v, A (bottomVector S)⟫) heq
  change ⟪v, (-S.1 * S.1 + R) (bottomEigenlineProjector S (bottomVector S)) + S.1 (W (bottomVector S))⟫ =
    ⟪v, sigma • bottomEigenlineProjector S (bottomVector S) + thirdEigenvalue S • W (bottomVector S) + F (bottomVector S)⟫ at he
  rw [hp, inner_add_right, inner_strainEquation_bottom S R _ hv,
    ← inner_strain_plane_eq S v _ hv] at he
  simp only [inner_add_right, real_inner_smul_right, hz, mul_zero, zero_add, hi] at he
  have hc := bottomGap_mul_norm_sq_le_rayleighExcess S v hv
  have he' : ⟪v, S.1 v⟫ - thirdEigenvalue S * ‖v‖ ^ 2 = -⟪v, (R - F) (bottomVector S)⟫ := by
    simp only [sub_apply, inner_sub_right]
    linarith
  rw [he', inner_remainder_bottom_eq_plane S (R - F) v hv] at hc
  have hb : -⟪v, expandingPlaneProjector S ((R - F) (bottomVector S))⟫ ≤
      ‖v‖ * ‖bottomCoupling S (R - F)‖ := by
    rw [norm_bottomCoupling]
    exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  rw [norm_bottomCoupling]
  change ‖v‖ ≤ _
  apply (le_div_iff₀ hg).mpr
  by_cases hzv : ‖v‖ = 0
  · rw [hzv, zero_mul]; exact norm_nonneg _
  · have hpv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzv)
    nlinarith

theorem norm_bottomCoupling_sub_smul_le (S : SymmetricStrain) (R F : Op) (c : ℝ) :
    ‖bottomCoupling S (R - c • F)‖ ≤ ‖bottomCoupling S R‖ + |c| * ‖bottomCoupling S F‖ := by
  have he : bottomCoupling S (R - c • F) = bottomCoupling S R - c • bottomCoupling S F := by
    apply ContinuousLinearMap.ext
    intro w
    simp only [bottomCoupling, mul_apply_eq_comp, sub_apply, smul_apply, map_sub, map_smul]
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le (bottomCoupling S R) (c • bottomCoupling S F)

theorem norm_bottomCoupling_le_of_parabolic_relation (S : SymmetricStrain) (R W G : Op)
    (sigma nu H : ℝ) (hg : 0 < bottomGap S) (hnu : 0 ≤ nu)
    (hG : ‖bottomCoupling S G‖ ≤ 2 * H / bottomGap S)
    (heq : (-S.1 * S.1 + R) * bottomEigenlineProjector S + S.1 * W =
      sigma • bottomEigenlineProjector S + thirdEigenvalue S • W + (2 * nu) • G) :
    ‖bottomCoupling S W‖ ≤
      ‖bottomCoupling S R‖ / bottomGap S + 4 * nu * H / bottomGap S ^ 2 := by
  calc
    _ ≤ ‖bottomCoupling S (R - (2 * nu) • G)‖ / bottomGap S :=
      norm_bottomCoupling_le_of_spectral_relation S R W _ sigma hg heq
    _ ≤ (‖bottomCoupling S R‖ + (2 * nu) * ‖bottomCoupling S G‖) / bottomGap S := by
      apply div_le_div_of_nonneg_right _ hg.le
      have h := norm_bottomCoupling_sub_smul_le S R G (2 * nu)
      rw [abs_of_nonneg (show 0 ≤ (2 : ℝ) * nu by positivity)] at h
      exact h
    _ ≤ (‖bottomCoupling S R‖ + (2 * nu) * (2 * H / bottomGap S)) / bottomGap S := by
      gcongr
    _ = _ := by field_simp; ring

end Mettapedia.FluidDynamics.NavierStokes.BottomParabolicProjectorMotion
