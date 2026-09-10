import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnisotropyDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedMaterialRate

/-!
# Anisotropy depletion relative to a multiple top eigenspace

Differentiability of the largest eigenvalue constrains the quadratic
compression of the strain rate on its whole top eigenspace. For a strain
equation `S' = -S² + R`, the remainder anisotropy therefore vanishes there.
The quantitative estimate measures distance from that eigenspace, rather
than distance from an arbitrary chosen line within it.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralClusterAnisotropy

open scoped Topology RealInnerProductSpace
open Filter PancakeAnisotropyDepletion PancakeSpectralDefectEvolution
open PancakeSpectralFiniteDifference PancakeRegularizedMaterialRate PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeStrainSpectralFrame PancakeEigenframePerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem abs_remainderAnisotropy_sub_le (R : H →L[ℝ] H) (e v w : H) (he : ‖e‖ = 1) :
    |remainderAnisotropy R e w - remainderAnisotropy R e v| ≤
      2 * ‖R‖ * (‖w‖ + ‖v‖) * ‖w - v‖ := by
  have hc : |⟪e, R e⟫| ≤ ‖R‖ := by
    simpa only [he, mul_one] using abs_inner_operator_le R e e
  have hid : remainderAnisotropy R e w - remainderAnisotropy R e v =
      ⟪e, R e⟫ * (⟪w - v, w⟫ + ⟪v, w - v⟫) -
        (⟪w - v, R w⟫ + ⟪v, R (w - v)⟫) := by
    simp only [remainderAnisotropy, inner_sub_left, inner_sub_right, map_sub,
      real_inner_self_eq_norm_sq]
    ring
  rw [hid]
  calc
    _ ≤ |⟪e, R e⟫| * (|⟪w - v, w⟫| + |⟪v, w - v⟫|) +
        (|⟪w - v, R w⟫| + |⟪v, R (w - v)⟫|) := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)) (abs_add_le _ _)
    _ ≤ ‖R‖ * (‖w - v‖ * ‖w‖ + ‖v‖ * ‖w - v‖) +
        (‖R‖ * ‖w - v‖ * ‖w‖ + ‖R‖ * ‖v‖ * ‖w - v‖) := by
      gcongr
      · exact abs_real_inner_le_norm _ _
      · exact abs_real_inner_le_norm _ _
      · exact abs_inner_operator_le _ _ _
      · exact abs_inner_operator_le _ _ _
    _ = _ := by ring

theorem abs_remainderAnisotropy_le_of_vanishing_projection
    (R : H →L[ℝ] H) (e v w : H) (he : ‖e‖ = 1)
    (hv : remainderAnisotropy R e v = 0) (hn : ‖v‖ ≤ ‖w‖) :
    |remainderAnisotropy R e w| ≤ 4 * ‖R‖ * ‖w‖ * ‖w - v‖ := by
  have h := abs_remainderAnisotropy_sub_le R e v w he
  rw [hv, sub_zero] at h
  calc
    _ ≤ 2 * ‖R‖ * (‖w‖ + ‖v‖) * ‖w - v‖ := h
    _ ≤ 2 * ‖R‖ * (‖w‖ + ‖w‖) * ‖w - v‖ := by gcongr
    _ = _ := by ring

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Homogeneous Rayleigh differentiation on the whole top eigenspace. -/
theorem topEigenvalue_rate_mul_norm_sq (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (rate t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (hL : HasDerivAt (fun τ ↦ topEigenvalue (S τ)) rate t)
    (v : R3) (hv : (S t).1 v = topEigenvalue (S t) • v) :
    rate * ‖v‖ ^ 2 = ⟪v, Sdot v⟫ := by
  have hq := (hasDerivAt_const t v).inner ℝ (hS.clm_apply (hasDerivAt_const t v))
  have hd := (hL.mul_const (‖v‖ ^ 2)).sub hq
  simp only [inner_zero_left, map_zero, add_zero] at hd
  have hz : topEigenvalue (S t) * ‖v‖ ^ 2 - ⟪v, (S t).1 v⟫ = 0 := by
    rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq, sub_self]
  have hm : IsLocalMin (fun τ ↦ topEigenvalue (S τ) * ‖v‖ ^ 2 - ⟪v, (S τ).1 v⟫) t := by
    apply Eventually.of_forall
    intro τ
    dsimp only
    rw [hz]
    exact topSpectralDefect_nonneg (S τ) v
  exact sub_eq_zero.mp (hm.hasDerivAt_eq_zero hd)

/-- The remainder's quadratic compression is scalar on the top eigenspace.
No normalization or continuous eigenvector choice is required. -/
theorem inner_remainder_top_eigenvector (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (rate t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (hL : HasDerivAt (fun τ ↦ topEigenvalue (S τ)) rate t)
    (v : R3) (hv : (S t).1 v = topEigenvalue (S t) • v) :
    ⟪v, R v⟫ = (rate + topEigenvalue (S t) ^ 2) * ‖v‖ ^ 2 := by
  have h := topEigenvalue_rate_mul_norm_sq S _ rate t hS hL v hv
  simp only [add_apply, mul_apply_eq_comp, neg_apply, hv, map_smul,
    inner_add_right, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  nlinarith [h]

theorem remainderAnisotropy_eq_zero_on_top_eigenspace (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (hL : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (v : R3) (hv : (S t).1 v = topEigenvalue (S t) • v) :
    remainderAnisotropy R (topVector (S t)) v = 0 := by
  have h1 := inner_remainder_top_eigenvector S R _ t hS hL.hasDerivAt v hv
  have h2 := inner_remainder_top_eigenvector S R _ t hS hL.hasDerivAt (topVector (S t))
    ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)
  rw [topVector_norm, one_pow, mul_one] at h2
  simp only [remainderAnisotropy, h1, h2, sub_self]

theorem expandingPlaneProjector_apply (S : SymmetricStrain) (w : R3) :
    expandingPlaneProjector S w =
      ⟪(orderedEigenframe S.1 S.2).eigenbasis 0, w⟫ • (orderedEigenframe S.1 S.2).eigenbasis 0 +
      ⟪(orderedEigenframe S.1 S.2).eigenbasis 1, w⟫ • (orderedEigenframe S.1 S.2).eigenbasis 1 := by
  simp only [expandingPlaneProjector, bottomEigenlineProjector, lineProjector,
    sub_apply, ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply]
  apply sub_eq_iff_eq_add.mpr
  simpa [Fin.sum_univ_succ, add_assoc]
    using ((orderedEigenframe S.1 S.2).eigenbasis.sum_repr' w).symm

theorem norm_expandingPlaneProjector_apply_le (S : SymmetricStrain) (w : R3) :
    ‖expandingPlaneProjector S w‖ ≤ ‖w‖ :=
  norm_lineRemainder_le ((orderedEigenframe S.1 S.2).eigenbasis 2) w
    ((orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 2)

theorem expandingPlaneProjector_is_top_of_topGap_zero (S : SymmetricStrain)
    (hg : topGap S = 0) (w : R3) :
    S.1 (expandingPlaneProjector S w) = topEigenvalue S • expandingPlaneProjector S w := by
  have h01 : (orderedEigenframe S.1 S.2).eigenvalue 1 = (orderedEigenframe S.1 S.2).eigenvalue 0 :=
    (sub_eq_zero.mp hg).symm
  rw [expandingPlaneProjector_apply]
  simp only [map_add, map_smul, (orderedEigenframe S.1 S.2).apply_eigenbasis, h01, topEigenvalue]
  module

theorem bottomGap_mul_norm_bottomEigenlineProjector_sq_le (S : SymmetricStrain) (w : R3) :
    bottomGap S * ‖bottomEigenlineProjector S w‖ ^ 2 ≤ topSpectralDefect S w := by
  have hn : ‖bottomEigenlineProjector S w‖ ^ 2 =
      ⟪w, (orderedEigenframe S.1 S.2).eigenbasis 2⟫ ^ 2 := by
    simp only [bottomEigenlineProjector, lineProjector, InnerProductSpace.rankOne_apply,
      norm_smul, Real.norm_eq_abs, (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one,
      mul_one, sq_abs, real_inner_comm]
  have hA := topSpectralDefect_coordinates S w
  change topSpectralDefect S w =
    topGap S * ⟪w, (orderedEigenframe S.1 S.2).eigenbasis 1⟫ ^ 2 +
      spectralWidth S * ⟪w, (orderedEigenframe S.1 S.2).eigenbasis 2⟫ ^ 2 at hA
  rw [hn, hA]
  exact (mul_le_mul_of_nonneg_right (bottomGap_le_spectralWidth S) (sq_nonneg _)).trans
    (le_add_of_nonneg_left (mul_nonneg (topGap_nonneg S) (sq_nonneg _)))

theorem norm_sub_expandingPlaneProjector_le (S : SymmetricStrain)
    (hg : 0 < bottomGap S) (w : R3) :
    ‖w - expandingPlaneProjector S w‖ ≤ Real.sqrt (topSpectralDefect S w / bottomGap S) := by
  have hq : ‖bottomEigenlineProjector S w‖ ^ 2 ≤ topSpectralDefect S w / bottomGap S :=
    (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using bottomGap_mul_norm_bottomEigenlineProjector_sq_le S w)
  simpa only [expandingPlaneProjector, sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
    using Real.le_sqrt_of_sq_le hq

/-- At a double top collision the quantitative depletion is controlled
by the bottom gap, not by a chosen line inside the top plane. -/
theorem abs_remainderAnisotropy_le_of_top_collision (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (hL : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (htop : topGap (S t) = 0) (hbottom : 0 < bottomGap (S t)) (w : R3) :
    |remainderAnisotropy R (topVector (S t)) w| ≤
      4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect (S t) w / bottomGap (S t)) := by
  have hv := remainderAnisotropy_eq_zero_on_top_eigenspace S R t hS hL
    (expandingPlaneProjector (S t) w) (expandingPlaneProjector_is_top_of_topGap_zero (S t) htop w)
  exact (abs_remainderAnisotropy_le_of_vanishing_projection R (topVector (S t)) _ w
    (topVector_norm (S t)) hv (norm_expandingPlaneProjector_apply_le (S t) w)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_expandingPlaneProjector_le (S t) hbottom w) (by positivity))

theorem apply_eq_topEigenvalue_smul_of_gaps_zero (S : SymmetricStrain)
    (htop : topGap S = 0) (hbottom : bottomGap S = 0) (w : R3) :
    S.1 w = topEigenvalue S • w := by
  have h01 : (orderedEigenframe S.1 S.2).eigenvalue 1 = (orderedEigenframe S.1 S.2).eigenvalue 0 :=
    (sub_eq_zero.mp htop).symm
  have h21 : (orderedEigenframe S.1 S.2).eigenvalue 2 = (orderedEigenframe S.1 S.2).eigenvalue 1 :=
    (sub_eq_zero.mp hbottom).symm
  have hw := (orderedEigenframe S.1 S.2).eigenbasis.sum_repr' w
  have h := congrArg (fun v : R3 ↦ S.1 v - topEigenvalue S • v) hw
  simp [Fin.sum_univ_succ, (orderedEigenframe S.1 S.2).apply_eigenbasis, h21, h01, topEigenvalue] at h
  have hz : S.1 w - topEigenvalue S • w = 0 := by
    change S.1 w - (orderedEigenframe S.1 S.2).eigenvalue 0 • w = 0
    rw [← h]
    module
  exact sub_eq_zero.mp hz

theorem remainderAnisotropy_eq_zero_of_triple_collision (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (hL : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (htop : topGap (S t) = 0) (hbottom : bottomGap (S t) = 0) (w : R3) :
    remainderAnisotropy R (topVector (S t)) w = 0 :=
  remainderAnisotropy_eq_zero_on_top_eigenspace S R t hS hL w
    (apply_eq_topEigenvalue_smul_of_gaps_zero (S t) htop hbottom w)

end Mettapedia.FluidDynamics.NavierStokes.SpectralClusterAnisotropy
