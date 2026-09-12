import Mettapedia.Analysis.EuclideanCrossProductCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Two-point cross-product evolution under incompressible strain

Common trace-free symmetric strain acts on a cross product with the opposite
sign. Unequal strains leave an explicit difference term. Neither the raw
cross product nor its normalized angle is asserted to decrease in general.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped RealInnerProductSpace Matrix
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem cross_mulVec_add_mulVec_cross (A : Matrix (Fin 3) (Fin 3) ℝ) (a b : R3) :
    cross (A.toEuclideanLin a) b + cross a (A.toEuclideanLin b) =
      A.trace • cross a b - A.transpose.toEuclideanLin (cross a b) := by
  ext i
  fin_cases i <;>
    simp [cross, cross_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Matrix.trace, Fin.sum_univ_three] <;> ring

theorem cross_mulVec_add_mulVec_cross_of_symmetric_trace_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.transpose = A) (htr : A.trace = 0) (a b : R3) :
    cross (A.toEuclideanLin a) b + cross a (A.toEuclideanLin b) =
      -A.toEuclideanLin (cross a b) := by
  rw [cross_mulVec_add_mulVec_cross, hA, htr, zero_smul, zero_sub]

theorem hasDerivAt_cross {a b : ℝ → R3} {a' b' : R3} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun τ ↦ cross (a τ) (b τ)) (cross a' (b t) + cross (a t) b') t := by
  have ha' (i : Fin 3) := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t ha
  have hb' (i : Fin 3) := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hb
  have hc (i j k l : Fin 3) : HasDerivAt (fun τ ↦ a τ i * b τ j - a τ k * b τ l)
      ((a' i * b t j + a t i * b' j) - (a' k * b t l + a t k * b' l)) t :=
    ((ha' i).mul (hb' j)).sub ((ha' k).mul (hb' l))
  have hcoord : HasDerivAt (fun τ ↦ WithLp.ofLp (cross (a τ) (b τ)))
      (WithLp.ofLp (cross a' (b t) + cross (a t) b')) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · apply (hc 1 2 2 1).congr_deriv
      simp [cross, cross_apply]
      ring
    · apply (hc 2 0 0 2).congr_deriv
      simp [cross, cross_apply]
      ring
    · apply (hc 0 1 1 0).congr_deriv
      simp [cross, cross_apply]
      ring
  let L := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv
  exact L.hasFDerivAt.comp_hasDerivAt t hcoord

/-- A squared sine, defined as zero when an endpoint vanishes. -/
def angleEnergy (a b : R3) : ℝ := ‖cross a b‖ ^ 2 / (‖a‖ ^ 2 * ‖b‖ ^ 2)

theorem angleEnergy_nonneg (a b : R3) : 0 ≤ angleEnergy a b := by
  unfold angleEnergy
  positivity

theorem angleEnergy_le_one (a b : R3) : angleEnergy a b ≤ 1 := by
  by_cases ha : a = 0
  · simp [angleEnergy, ha]
  by_cases hb : b = 0
  · simp [angleEnergy, hb]
  have hd : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr ha))
    (sq_pos_of_pos (norm_pos_iff.mpr hb))
  rw [angleEnergy, div_le_one hd, norm_cross_sq]
  nlinarith [sq_nonneg ⟪a, b⟫]

theorem hasDerivAt_angleEnergy {a b : ℝ → R3} {a' b' : R3} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (ha0 : a t ≠ 0) (hb0 : b t ≠ 0) :
    HasDerivAt (fun τ ↦ angleEnergy (a τ) (b τ))
      (2 * ⟪cross (a t) (b t), cross a' (b t) + cross (a t) b'⟫ /
          (‖a t‖ ^ 2 * ‖b t‖ ^ 2) -
        2 * angleEnergy (a t) (b t) *
          (⟪a t, a'⟫ / ‖a t‖ ^ 2 + ⟪b t, b'⟫ / ‖b t‖ ^ 2)) t := by
  have hna : ‖a t‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hnb : ‖b t‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
  have h := ((hasDerivAt_cross ha hb).norm_sq).div (ha.norm_sq.mul hb.norm_sq)
    (mul_ne_zero (pow_ne_zero 2 hna) (pow_ne_zero 2 hnb))
  apply h.congr_deriv
  simp only [angleEnergy, Pi.mul_apply]
  field_simp [hna, hnb]

end Mettapedia.Analysis.EuclideanCrossProduct
