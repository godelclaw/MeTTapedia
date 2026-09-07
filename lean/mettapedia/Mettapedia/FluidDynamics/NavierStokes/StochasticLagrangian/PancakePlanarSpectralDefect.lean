import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact spectral defect for a planar incompressible strain

For the strain matrix with planar block `[[a,b],[b,-a]]` and zero
third row and column, the largest eigenvalue is `sqrt (a^2+b^2)`.
The vorticity of a planar velocity is normal to this block, so its
spectral defect is exactly `sqrt (a^2+b^2) * w^2`.

This reduction retains the constructed three-dimensional top eigenvalue.
It will be used to test the sign of the physical diffusion contribution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePlanarSpectralDefect

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def planarMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b, 0; b, -a, 0; 0, 0, 0]

def planarOperator (a b : ℝ) : R3 →L[ℝ] R3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (planarMatrix a b)

theorem planarOperator_apply (a b : ℝ) (v : R3) :
    planarOperator a b v = WithLp.toLp 2 ![a * v 0 + b * v 1,
      b * v 0 - a * v 1, 0] := by
  ext i
  change Matrix.mulVec (planarMatrix a b) (WithLp.ofLp v) i = _
  fin_cases i <;> simp [planarMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem planarOperator_symmetric (a b : ℝ) :
    ∀ v w : R3, ⟪v, planarOperator a b w⟫ = ⟪planarOperator a b v, w⟫ := by
  have hh : (planarMatrix a b).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planarMatrix, Matrix.conjTranspose_apply]
  intro v w
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hh v w).symm

def planarStrain (a b : ℝ) : SymmetricStrain :=
  ⟨planarOperator a b, planarOperator_symmetric a b⟩

def normalVorticity (w : ℝ) : R3 := WithLp.toLp 2 ![0, 0, w]

theorem normalVorticity_norm_sq (w : ℝ) : ‖normalVorticity w‖ ^ 2 = w ^ 2 := by
  simp [normalVorticity, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem planarOperator_normalVorticity (a b w : ℝ) :
    planarOperator a b (normalVorticity w) = 0 := by
  rw [planarOperator_apply]
  ext i
  fin_cases i <;> simp [normalVorticity]

theorem planarOperator_norm_sq (a b : ℝ) (v : R3) :
    ‖planarOperator a b v‖ ^ 2 = (a ^ 2 + b ^ 2) * ((v 0) ^ 2 + (v 1) ^ 2) := by
  rw [planarOperator_apply]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

theorem topEigenvalue_planarStrain (a b : ℝ) (ha : 0 < a) :
    topEigenvalue (planarStrain a b) = Real.sqrt (a ^ 2 + b ^ 2) := by
  let S := planarStrain a b
  let r := Real.sqrt (a ^ 2 + b ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  apply le_antisymm
  · let e := (orderedEigenframe S.1 S.2).eigenbasis 0
    have he : ‖e‖ = 1 := (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 0
    have hp : planarOperator a b e = topEigenvalue S • e :=
      (orderedEigenframe S.1 S.2).apply_eigenbasis 0
    have hn := planarOperator_norm_sq a b e
    rw [hp, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs] at hn
    have hs : (e 0) ^ 2 + (e 1) ^ 2 + (e 2) ^ 2 = 1 := by
      have he2 : ‖e‖ ^ 2 = 1 := by rw [he]; norm_num
      simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] using he2
    change topEigenvalue S ≤ r
    nlinarith [sq_nonneg (e 2), sq_nonneg b]
  · let v : R3 := WithLp.toLp 2 ![r + a, b, 0]
    have hv : ‖v‖ ^ 2 > 0 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      change 0 < (r + a) ^ 2 + b ^ 2 + (0 : ℝ) ^ 2
      positivity
    have hp : planarOperator a b v = r • v := by
      rw [planarOperator_apply]
      ext i
      fin_cases i <;> simp [v] <;> nlinarith
    have h := PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq S.1 S.2 v
    change ⟪v, planarOperator a b v⟫ ≤ topEigenvalue S * ‖v‖ ^ 2 at h
    rw [hp, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    exact (mul_le_mul_iff_left₀ hv).mp h

def planarDefect (a b w : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2) * w ^ 2

theorem topEigenvalue_offDiagonal (b : ℝ) :
    topEigenvalue (planarStrain 0 b) = |b| := by
  let S := planarStrain 0 b
  apply le_antisymm
  · let e := (orderedEigenframe S.1 S.2).eigenbasis 0
    have he : ‖e‖ = 1 := (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 0
    have hp : planarOperator 0 b e = topEigenvalue S • e :=
      (orderedEigenframe S.1 S.2).apply_eigenbasis 0
    have hn := planarOperator_norm_sq 0 b e
    rw [hp, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs] at hn
    have he2 : ‖e‖ ^ 2 = 1 := by rw [he]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at he2
    change topEigenvalue S ≤ |b|
    nlinarith [sq_nonneg (e 2), sq_nonneg b, abs_nonneg b, sq_abs b]
  · let v : R3 := WithLp.toLp 2 ![1, if 0 ≤ b then 1 else -1, 0]
    have hv : ‖v‖ ^ 2 = 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      change (1 : ℝ) ^ 2 + (if 0 ≤ b then (1 : ℝ) else -1) ^ 2 + (0 : ℝ) ^ 2 = 2
      split_ifs <;> norm_num
    have hp : planarOperator 0 b v = |b| • v := by
      rw [planarOperator_apply]
      by_cases hb : 0 ≤ b
      · ext i; fin_cases i <;> simp [v, hb, abs_of_nonneg hb]
      · ext i; fin_cases i <;> simp [v, hb, abs_of_neg (lt_of_not_ge hb)]
    have h := PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq S.1 S.2 v
    change ⟪v, planarOperator 0 b v⟫ ≤ topEigenvalue S * ‖v‖ ^ 2 at h
    rw [hp, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at h
    linarith

theorem topSpectralDefect_planar (a b w : ℝ) (ha : 0 < a) :
    topSpectralDefect (planarStrain a b) (normalVorticity w) = planarDefect a b w := by
  rw [topSpectralDefect, spectralDefect, topEigenvalue_planarStrain a b ha,
    normalVorticity_norm_sq]
  change _ - ⟪normalVorticity w, planarOperator a b (normalVorticity w)⟫ = _
  rw [planarOperator_normalVorticity, inner_zero_right, sub_zero]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.PancakePlanarSpectralDefect
