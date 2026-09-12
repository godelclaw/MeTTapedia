import Mettapedia.Analysis.SymmetricCrossProductStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution

/-!
# Two-point angle growth charged to top spectral defects

The bottom eigenvalue of trace-free three-dimensional strain equals its
top gap minus twice its top eigenvalue. Symmetric endpoint averaging
therefore retains top-gap damping, opposed by the normalized top spectral
defects and a signed perturbation. Neither coherence nor a perturbation
budget is assumed or supplied by this estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy
open PancakeSpectralClusterDichotomy.SymmetricStrain StrainEigenvalueContinuity
open PancakeSpectralDefectEvolution PancakeTransverseEnergyCoercivity
open Mettapedia.Analysis.EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem thirdEigenvalue_mul_norm_sq_le_rayleigh (S : SymmetricStrain) (w : R3) :
    thirdEigenvalue S * ‖w‖ ^ 2 ≤ ⟪w, S.1 w⟫ := by
  let F := orderedEigenframe S.1 S.2
  have h20 : F.eigenvalue 2 ≤ F.eigenvalue 0 := F.antitone_eigenvalue (by decide)
  have h21 : F.eigenvalue 2 ≤ F.eigenvalue 1 := F.antitone_eigenvalue (by decide)
  have hparse := parseval_three_norm_sq F.eigenbasis w
  have hray := rayleigh_three S.1 S.2 F.eigenvalue F.eigenbasis F.apply_eigenbasis w
  change F.eigenvalue 2 * ‖w‖ ^ 2 ≤ _
  rw [← hparse, hray]
  calc
    _ = F.eigenvalue 2 * ⟪w, F.eigenbasis 0⟫ ^ 2 +
        F.eigenvalue 2 * ⟪w, F.eigenbasis 1⟫ ^ 2 +
        F.eigenvalue 2 * ⟪w, F.eigenbasis 2⟫ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem topGap_sub_two_topEigenvalue_le_rayleigh (S : SymmetricStrain)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0) (w : R3) :
    (topGap S - 2 * topEigenvalue S) * ‖w‖ ^ 2 ≤ ⟪w, S.1 w⟫ := by
  rw [trace_eq_sum_orderedEigenvalues] at htrace
  have heq : topGap S - 2 * topEigenvalue S = thirdEigenvalue S := by
    unfold topGap
    linarith
  rw [heq]
  exact thirdEigenvalue_mul_norm_sq_le_rayleigh S w

theorem neg_two_topEigenvalue_le_rayleigh (S : SymmetricStrain)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0) (w : R3) :
    -2 * topEigenvalue S * ‖w‖ ^ 2 ≤ ⟪w, S.1 w⟫ := by
  rw [trace_eq_sum_orderedEigenvalues] at htrace
  let F := orderedEigenframe S.1 S.2
  have h01 : F.eigenvalue 1 ≤ F.eigenvalue 0 := F.antitone_eigenvalue (by decide)
  have h12 : F.eigenvalue 2 ≤ F.eigenvalue 1 := F.antitone_eigenvalue (by decide)
  change F.eigenvalue 0 + F.eigenvalue 1 + F.eigenvalue 2 = 0 at htrace
  have h0 : -2 * F.eigenvalue 0 ≤ F.eigenvalue 0 := by linarith
  have h1 : -2 * F.eigenvalue 0 ≤ F.eigenvalue 1 := by linarith
  have h2 : -2 * F.eigenvalue 0 ≤ F.eigenvalue 2 := by linarith
  have hparse := parseval_three_norm_sq F.eigenbasis w
  have hray := rayleigh_three S.1 S.2 F.eigenvalue F.eigenbasis F.apply_eigenbasis w
  change -2 * F.eigenvalue 0 * ‖w‖ ^ 2 ≤ _
  rw [← hparse, hray]
  calc
    _ = (-2 * F.eigenvalue 0) * ⟪w, F.eigenbasis 0⟫ ^ 2 +
        (-2 * F.eigenvalue 0) * ⟪w, F.eigenbasis 1⟫ ^ 2 +
        (-2 * F.eigenvalue 0) * ⟪w, F.eigenbasis 2⟫ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem commonStrain_angleRate_le_defects (S : SymmetricStrain)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (a b : R3) (ha : a ≠ 0) (hb : b ≠ 0) :
    angleRate S.1 S.1 a b 0 0 ≤
      2 * (topSpectralDefect S a / ‖a‖ ^ 2 + topSpectralDefect S b / ‖b‖ ^ 2) *
        angleEnergy a b := by
  have hna : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hnb : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hr := neg_two_topEigenvalue_le_rayleigh S htrace (cross a b)
  have hdiv := (div_le_div_iff_of_pos_right (mul_pos hna hnb)).2
    (show -2 * ⟪cross a b, S.1 (cross a b)⟫ ≤
      4 * topEigenvalue S * ‖cross a b‖ ^ 2 by linarith)
  simp only [angleRate, pairForcing, sub_self, zero_apply, cross_zero, zero_cross,
    add_zero, inner_zero_right, mul_zero, zero_div]
  calc
    _ ≤ 4 * topEigenvalue S * ‖cross a b‖ ^ 2 / (‖a‖ ^ 2 * ‖b‖ ^ 2) -
        2 * angleEnergy a b * (⟪a, S.1 a⟫ / ‖a‖ ^ 2 + ⟪b, S.1 b⟫ / ‖b‖ ^ 2) :=
      sub_le_sub_right hdiv _
    _ = _ := by
      unfold topSpectralDefect spectralDefect angleEnergy
      field_simp [ne_of_gt hna, ne_of_gt hnb]
      ring

theorem angleRate_le_defects_add_perturbation (S : SymmetricStrain)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (T : R3 →L[ℝ] R3) (a b f g : R3) (ha : a ≠ 0) (hb : b ≠ 0) :
    angleRate S.1 T a b f g ≤
      2 * (topSpectralDefect S a / ‖a‖ ^ 2 + topSpectralDefect S b / ‖b‖ ^ 2) *
        angleEnergy a b + anglePerturbation S.1 T a b f g := by
  rw [angleRate_eq_common_add_perturbation]
  linarith [commonStrain_angleRate_le_defects S htrace a b ha hb]

/-- The negative top-gap terms survive symmetric averaging. -/
theorem symmetricAngleRate_le_gap_damping (S T : SymmetricStrain)
    (hS : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (hT : LinearMap.trace ℝ R3 T.1.toLinearMap = 0)
    (a b f g : R3) (ha : a ≠ 0) (hb : b ≠ 0) :
    symmetricAngleRate S.1 T.1 a b f g ≤
      (2 * (topSpectralDefect S a / ‖a‖ ^ 2 + topSpectralDefect T b / ‖b‖ ^ 2) -
        (topGap S + topGap T)) *
        angleEnergy a b + symmetricAnglePerturbation S.1 T.1 a b f g := by
  have hna : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hnb : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hs := topGap_sub_two_topEigenvalue_le_rayleigh S hS (cross a b)
  have ht := topGap_sub_two_topEigenvalue_le_rayleigh T hT (cross a b)
  have hdiv := (div_le_div_iff_of_pos_right (mul_pos hna hnb)).2
    (show -(⟪cross a b, S.1 (cross a b)⟫ + ⟪cross a b, T.1 (cross a b)⟫) ≤
      (2 * (topEigenvalue S + topEigenvalue T) - (topGap S + topGap T)) *
        ‖cross a b‖ ^ 2 by nlinarith)
  have heq :
      (2 * (topEigenvalue S + topEigenvalue T) - (topGap S + topGap T)) *
          ‖cross a b‖ ^ 2 / (‖a‖ ^ 2 * ‖b‖ ^ 2) -
        2 * angleEnergy a b * (⟪a, S.1 a⟫ / ‖a‖ ^ 2 + ⟪b, T.1 b⟫ / ‖b‖ ^ 2) =
      (2 * (topSpectralDefect S a / ‖a‖ ^ 2 + topSpectralDefect T b / ‖b‖ ^ 2) -
        (topGap S + topGap T)) *
        angleEnergy a b := by
    unfold topSpectralDefect spectralDefect angleEnergy
    field_simp [ne_of_gt hna, ne_of_gt hnb]
    ring
  unfold symmetricAngleRate
  linarith

/-- Dropping the nonnegative gap damping gives the weaker pure-growth bound. -/
theorem symmetricAngleRate_le_endpointDefects (S T : SymmetricStrain)
    (hS : LinearMap.trace ℝ R3 S.1.toLinearMap = 0)
    (hT : LinearMap.trace ℝ R3 T.1.toLinearMap = 0)
    (a b f g : R3) (ha : a ≠ 0) (hb : b ≠ 0) :
    symmetricAngleRate S.1 T.1 a b f g ≤
      2 * (topSpectralDefect S a / ‖a‖ ^ 2 + topSpectralDefect T b / ‖b‖ ^ 2) *
        angleEnergy a b + symmetricAnglePerturbation S.1 T.1 a b f g := by
  have h := symmetricAngleRate_le_gap_damping S T hS hT a b f g ha hb
  have hg : 0 ≤ (topGap S + topGap T) * angleEnergy a b :=
    mul_nonneg (add_nonneg (topGap_nonneg S) (topGap_nonneg T)) (angleEnergy_nonneg a b)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle
