import Mettapedia.Analysis.CrossProductEvolution
import Mettapedia.Analysis.SignedCrossKernel

/-!
# Scalar triple products under a common deformation

The scalar triple product of two vectors and their separation has a
common-deformation rate equal to the trace times the triple product.
For incompressible deformation this part cancels exactly, without a
symmetry assumption on the gradient. Unequal deformation and external
rates are retained as explicit residuals.

For a scalar identity plus a radial rank-one operator, the signed
stretching kernel contains this triple product, not the norm of the
cross product. Applying this formula to a particular kernel requires
proving its decomposition; no radiality of a periodic kernel is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped RealInnerProductSpace Matrix
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def tripleProduct (a b h : R3) : ℝ := ⟪cross a b, h⟫

def tripleRate (a b h da db dh : R3) : ℝ :=
  ⟪cross da b + cross a db, h⟫ + ⟪cross a b, dh⟫

theorem hasDerivAt_tripleProduct {a b h : ℝ → R3} {da db dh : R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun τ ↦ tripleProduct (a τ) (b τ) (h τ))
      (tripleRate (a t) (b t) (h t) da db dh) t := by
  simpa only [tripleProduct, tripleRate, add_comm] using (hasDerivAt_cross ha hb).inner ℝ hh

theorem tripleRate_common (A : Matrix (Fin 3) (Fin 3) ℝ) (a b h : R3) :
    tripleRate a b h (A.toEuclideanLin a) (A.toEuclideanLin b) (A.toEuclideanLin h) =
      A.trace * tripleProduct a b h := by
  rw [tripleRate, cross_mulVec_add_mulVec_cross]
  simp only [tripleProduct, inner_sub_left, real_inner_smul_left]
  have ht : ⟪A.transpose.toEuclideanLin (cross a b), h⟫ =
      ⟪cross a b, A.toEuclideanLin h⟫ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.toLpLin_apply, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [ht]
  ring

theorem tripleRate_add (a b h da db dh ra rb rh : R3) :
    tripleRate a b h (da + ra) (db + rb) (dh + rh) =
      tripleRate a b h da db dh + tripleRate a b h ra rb rh := by
  simp only [tripleRate, cross_add_left, cross_add_right, inner_add_left, inner_add_right]
  ring

theorem tripleRate_cancel_common (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.trace = 0) (a b h ra rb rh : R3) :
    tripleRate a b h (A.toEuclideanLin a + ra) (A.toEuclideanLin b + rb)
      (A.toEuclideanLin h + rh) = tripleRate a b h ra rb rh := by
  rw [tripleRate_add, tripleRate_common, hA, zero_mul, zero_add]

theorem abs_tripleProduct_le (a b h : R3) :
    |tripleProduct a b h| ≤ ‖a‖ * ‖b‖ * ‖h‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_cross_le a b) (norm_nonneg h))

theorem abs_tripleRate_le (a b h ra rb rh : R3) :
    |tripleRate a b h ra rb rh| ≤
      (‖ra‖ * ‖b‖ + ‖a‖ * ‖rb‖) * ‖h‖ + ‖a‖ * ‖b‖ * ‖rh‖ := by
  unfold tripleRate
  rw [inner_add_left]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_tripleProduct_le ra b h)
      (abs_tripleProduct_le a rb h)))
    (abs_tripleProduct_le a b rh)) |>.trans_eq (by ring)

/-- No nonvanishing hypothesis is needed, even at zero separation. -/
def radialOperator (c d : ℝ) (h : R3) : R3 →L[ℝ] R3 :=
  c • ContinuousLinearMap.id ℝ R3 + d • (innerSL ℝ h).smulRight h

theorem pairedStretch_radialOperator (n : ℕ) (c d : ℝ) (h a b : R3) :
    SignedCrossKernel.pairedStretch n (radialOperator c d h) a b =
      d * tripleProduct a b h * ⟪h, RadialPower.radialPower n a - RadialPower.radialPower n b⟫ := by
  rw [radialOperator, add_comm, SignedCrossKernel.pairedStretch_add_scalar_identity]
  simp only [SignedCrossKernel.pairedStretch, smul_apply,
    ContinuousLinearMap.smulRight_apply, real_inner_smul_right,
    tripleProduct]
  change d * (⟪h, RadialPower.radialPower n a - RadialPower.radialPower n b⟫ *
    ⟪cross a b, h⟫) = _
  ring

end Mettapedia.Analysis.EuclideanCrossProduct
