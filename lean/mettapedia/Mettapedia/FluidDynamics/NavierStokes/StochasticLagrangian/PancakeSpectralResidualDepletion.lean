import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution

/-!
# Spectral residual bounded by the gap-weighted defect

The squared spectral residual is at most the spectral width times the
Rayleigh defect. This estimate uses no inverse spectral gap and remains
valid at eigenvalue collisions. It vanishes on the entire top eigenspace.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralResidualDepletion

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def spectralWidth (S : SymmetricStrain) : ℝ :=
  (orderedEigenframe S.1 S.2).eigenvalue 0 - (orderedEigenframe S.1 S.2).eigenvalue 2

theorem spectralWidth_nonneg (S : SymmetricStrain) : 0 ≤ spectralWidth S :=
  sub_nonneg.mpr ((orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide : (0 : Fin 3) ≤ 2))

theorem abs_orderedEigenvalue_le_opNorm (S : SymmetricStrain) (i : Fin 3) :
    |(orderedEigenframe S.1 S.2).eigenvalue i| ≤ ‖S.1‖ := by
  have h := S.1.le_opNorm ((orderedEigenframe S.1 S.2).eigenbasis i)
  simpa only [(orderedEigenframe S.1 S.2).apply_eigenbasis, norm_smul, Real.norm_eq_abs,
    (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one, mul_one] using h

theorem spectralWidth_le_twice_opNorm (S : SymmetricStrain) :
    spectralWidth S ≤ 2 * ‖S.1‖ := by
  have h0 := abs_le.mp (abs_orderedEigenvalue_le_opNorm S 0)
  have h2 := abs_le.mp (abs_orderedEigenvalue_le_opNorm S 2)
  unfold spectralWidth
  linarith

theorem norm_topSpectralResidual_sq_le_width_defect (S : SymmetricStrain) (w : R3) :
    ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 ≤
      spectralWidth S * topSpectralDefect S w := by
  let F := orderedEigenframe S.1 S.2
  have h01 : 0 ≤ F.eigenvalue 0 - F.eigenvalue 1 :=
    sub_nonneg.mpr (F.antitone_eigenvalue (by decide : (0 : Fin 3) ≤ 1))
  have h12 : 0 ≤ F.eigenvalue 1 - F.eigenvalue 2 :=
    sub_nonneg.mpr (F.antitone_eigenvalue (by decide : (1 : Fin 3) ≤ 2))
  have h := mul_nonneg (mul_nonneg h01 h12) (sq_nonneg ⟪w, F.eigenbasis 1⟫)
  rw [norm_topSpectralResidual_sq_coordinates, topSpectralDefect_coordinates]
  change (F.eigenvalue 0 - F.eigenvalue 1) ^ 2 * ⟪w, F.eigenbasis 1⟫ ^ 2 +
    (F.eigenvalue 0 - F.eigenvalue 2) ^ 2 * ⟪w, F.eigenbasis 2⟫ ^ 2 ≤
    (F.eigenvalue 0 - F.eigenvalue 2) *
      ((F.eigenvalue 0 - F.eigenvalue 1) * ⟪w, F.eigenbasis 1⟫ ^ 2 +
        (F.eigenvalue 0 - F.eigenvalue 2) * ⟪w, F.eigenbasis 2⟫ ^ 2)
  nlinarith

theorem norm_topSpectralResidual_sq_le_opNorm_defect (S : SymmetricStrain) (w : R3) :
    ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 ≤
      2 * ‖S.1‖ * topSpectralDefect S w :=
  (norm_topSpectralResidual_sq_le_width_defect S w).trans
    (mul_le_mul_of_nonneg_right (spectralWidth_le_twice_opNorm S) (topSpectralDefect_nonneg S w))

theorem topSpectralResidual_eq_zero_of_defect_eq_zero (S : SymmetricStrain) (w : R3)
    (h : topSpectralDefect S w = 0) : spectralResidual S.1 (topEigenvalue S) w = 0 := by
  have hb := norm_topSpectralResidual_sq_le_width_defect S w
  rw [h, mul_zero] at hb
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (spectralResidual S.1 (topEigenvalue S) w)])

theorem topSpectralDefect_eq_zero_iff (S : SymmetricStrain) (w : R3) :
    topSpectralDefect S w = 0 ↔ spectralResidual S.1 (topEigenvalue S) w = 0 := by
  constructor
  · exact topSpectralResidual_eq_zero_of_defect_eq_zero S w
  · intro h
    simp only [topSpectralDefect, spectralDefect_eq_inner, h, inner_zero_right]

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralResidualDepletion
