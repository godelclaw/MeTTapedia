import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyEnvelope
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Transverse source forcing controlled by a strain commutator

The linear-in-misalignment part of the quadratic anisotropy is controlled
by the commutator with strain. The remaining part is quadratic in the
line remainder. No symmetry of the source operator is required: the two
off-diagonal blocks are controlled using its adjoint. The strain is symmetric.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralSourceCommutator

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeAnisotropyDepletion
open PancakeSpectralResidualDepletion SpectralAnisotropyEnvelope

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def commutator (S : SymmetricStrain) (R : R3 →L[ℝ] R3) : R3 →L[ℝ] R3 :=
  S.1 * R - R * S.1

theorem commutator_add (S : SymmetricStrain) (R Q : R3 →L[ℝ] R3) :
    commutator S (R + Q) = commutator S R + commutator S Q := by
  unfold commutator
  noncomm_ring

theorem commutator_neg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    commutator S (-R) = -commutator S R := by
  ext v
  simp only [commutator, sub_apply, mul_apply_eq_comp, neg_apply, map_neg, neg_sub]
  abel_nf

theorem commutator_smul (S : SymmetricStrain) (a : ℝ) (R : R3 →L[ℝ] R3) :
    commutator S (a • R) = a • commutator S R := by
  ext v
  simp only [commutator, sub_apply, mul_apply_eq_comp, smul_apply, map_smul, smul_sub]

theorem commutator_sum {ι : Type*} (S : SymmetricStrain)
    (I : Finset ι) (R : ι → R3 →L[ℝ] R3) :
    commutator S (∑ i ∈ I, R i) = ∑ i ∈ I, commutator S (R i) := by
  simp only [commutator, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem commutator_mul (S : SymmetricStrain) (R Q : R3 →L[ℝ] R3) :
    commutator S (R * Q) = commutator S R * Q + R * commutator S Q := by
  simp only [commutator, sub_mul, mul_sub, mul_assoc]
  abel

theorem commutator_self (S : SymmetricStrain) : commutator S S.1 = 0 := sub_self _

theorem commutator_isotropic (S : SymmetricStrain) (a : ℝ) :
    commutator S (a • (1 : R3 →L[ℝ] R3)) = 0 := by
  ext v
  simp only [commutator, sub_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self,
    map_smul, sub_self, zero_apply]

theorem topGap_mul_norm_lineRemainder_le (S : SymmetricStrain) (v : R3) :
    topGap S * ‖lineRemainder (topVector S) v‖ ≤
      ‖spectralResidual S.1 (topEigenvalue S) v‖ := by
  have h := mul_le_mul_of_nonneg_left (topGap_mul_lineRemainder_sq_le S v) (topGap_nonneg S)
  have hz := topGap_mul_defect_le_norm_topSpectralResidual_sq S v
  have hp := mul_nonneg (topGap_nonneg S) (norm_nonneg (lineRemainder (topVector S) v))
  nlinarith [norm_nonneg (spectralResidual S.1 (topEigenvalue S) v)]

theorem residual_source_topVector (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    spectralResidual S.1 (topEigenvalue S) (R (topVector S)) =
      -(commutator S R (topVector S)) := by
  have he : S.1 (topVector S) = topEigenvalue S • topVector S :=
    (PancakeStrainSpectralFrame.orderedEigenframe S.1 S.2).apply_eigenbasis 0
  simp only [spectralResidual, commutator, sub_apply,
    mul_apply_eq_comp, he, map_smul, neg_sub]

theorem topGap_mul_norm_transverse_source_le (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    topGap S * ‖lineRemainder (topVector S) (R (topVector S))‖ ≤ ‖commutator S R‖ := by
  have h := topGap_mul_norm_lineRemainder_le S (R (topVector S))
  rw [residual_source_topVector, norm_neg] at h
  exact h.trans (by simpa only [topVector_norm, mul_one] using
    (commutator S R).le_opNorm (topVector S))

theorem norm_commutator_adjoint (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    ‖commutator S R.adjoint‖ = ‖commutator S R‖ := by
  have hs : S.1.adjoint = S.1 :=
    ((ContinuousLinearMap.eq_adjoint_iff S.1 S.1).mpr (fun x y ↦ (S.2 x y).symm)).symm
  have he : commutator S R.adjoint = -(commutator S R).adjoint := by
    simp only [commutator, map_sub, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp, hs, neg_sub]
  rw [he, norm_neg]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem norm_transverse_source_le (S : SymmetricStrain) (R : R3 →L[ℝ] R3) :
    ‖lineRemainder (topVector S) (R (topVector S))‖ ≤ ‖R‖ :=
  (norm_lineRemainder_le _ _ (topVector_norm S)).trans
    (by simpa only [topVector_norm, mul_one] using R.le_opNorm (topVector S))

theorem norm_transverse_source_le_regularized (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ‖lineRemainder (topVector S) (R (topVector S))‖ ≤
      (‖commutator S R‖ + epsilon * ‖R‖) / (topGap S + epsilon) := by
  apply (le_div_iff₀ (add_pos_of_nonneg_of_pos (topGap_nonneg S) heps)).mpr
  have h := topGap_mul_norm_transverse_source_le S R
  have h' := mul_le_mul_of_nonneg_left (norm_transverse_source_le S R) heps.le
  nlinarith only [h, h']

theorem inner_lineRemainder_left (e w v : R3) (he : ‖e‖ = 1) :
    ⟪lineRemainder e w, lineRemainder e v⟫ = ⟪lineRemainder e w, v⟫ := by
  simp only [lineRemainder, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, he, real_inner_comm w e]
  ring

theorem abs_anisotropy_le_transverse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    |remainderAnisotropy R (topVector S) w| ≤
      2 * ‖R‖ * ‖lineRemainder (topVector S) w‖ ^ 2 +
      ‖w‖ * ‖lineRemainder (topVector S) w‖ *
        (‖lineRemainder (topVector S) (R (topVector S))‖ +
         ‖lineRemainder (topVector S) (R.adjoint (topVector S))‖) := by
  let e := topVector S
  let m := lineRemainder e w
  have he : ‖e‖ = 1 := topVector_norm S
  have ha : |⟪e, w⟫| ≤ ‖w‖ := by simpa only [he, one_mul] using abs_real_inner_le_norm e w
  have h1 : |⟪e, R m⟫| ≤ ‖m‖ * ‖lineRemainder e (R.adjoint e)‖ := by
    rw [← ContinuousLinearMap.adjoint_inner_left R m e, real_inner_comm]
    rw [← inner_lineRemainder_left e w (R.adjoint e) he]
    exact abs_real_inner_le_norm _ _
  have h2 : |⟪m, R e⟫| ≤ ‖m‖ * ‖lineRemainder e (R e)‖ := by
    rw [← inner_lineRemainder_left e w (R e) he]
    exact abs_real_inner_le_norm _ _
  rw [remainderAnisotropy_line_expansion R e w he]
  calc
    _ ≤ |remainderAnisotropy R e m| +
        |⟪e, w⟫| * (|⟪e, R m⟫| + |⟪m, R e⟫|) := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      gcongr
      exact abs_add_le _ _
    _ ≤ 2 * ‖R‖ * ‖m‖ ^ 2 + ‖w‖ *
        (‖m‖ * ‖lineRemainder e (R.adjoint e)‖ + ‖m‖ * ‖lineRemainder e (R e)‖) :=
      add_le_add (abs_remainderAnisotropy_le R e m he)
        (mul_le_mul ha (add_le_add h1 h2) (by positivity) (norm_nonneg w))
    _ = _ := by dsimp only [m, e]; ring

theorem abs_anisotropy_le_regularized_commutator (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) :
    |remainderAnisotropy R (topVector S) w| ≤
      2 * ‖R‖ * ‖lineRemainder (topVector S) w‖ ^ 2 +
      2 * ((‖commutator S R‖ + epsilon * ‖R‖) / (topGap S + epsilon)) *
        ‖w‖ * ‖lineRemainder (topVector S) w‖ := by
  have h1 := norm_transverse_source_le_regularized S R epsilon heps
  have h2 := norm_transverse_source_le_regularized S R.adjoint epsilon heps
  rw [norm_commutator_adjoint, ContinuousLinearMap.adjoint.norm_map] at h2
  apply (abs_anisotropy_le_transverse S R w).trans
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (mul_nonneg (norm_nonneg w) (norm_nonneg (lineRemainder (topVector S) w)))
  nlinarith only [h]

theorem continuous_commutator {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3)
    (hS : Continuous S) (hR : Continuous R) : Continuous (fun x ↦ commutator (S x) (R x)) :=
  ((continuous_subtype_val.comp hS).mul hR).sub (hR.mul (continuous_subtype_val.comp hS))

end Mettapedia.FluidDynamics.NavierStokes.SpectralSourceCommutator
