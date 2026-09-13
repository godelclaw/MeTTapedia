import Mettapedia.Analysis.CurlCrossProduct
import Mettapedia.Analysis.RadialPowerCurvature
import Mettapedia.Analysis.AngularCurlDecomposition

/-!
# Removing the exact gradient from octic curl work

The transverse curl of the radial field `‖a‖⁶ a` consists of an
explicit scalar gradient and a derivative along `a`. The identity also
retains the curl of any difference between a test and that radial field.
All formulas remain valid at zero and require no normalized direction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.OcticCurlCancellation

open scoped RealInnerProductSpace
open EuclideanCrossProduct WeightedCurlCancellation RadialPower
open AngularCurlDecomposition
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem cross_curlJet (a : R3) (D : Fin 3 → R3) :
    cross a (curlJet D) = WithLp.toLp 2 (fun j ↦ ⟪a, D j⟫) - ∑ j, a j • D j := by
  ext i
  fin_cases i <;>
    simp [cross, cross_apply, curlJet, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three] <;> ring

def potential (a : R3) : ℝ := (7 / 8 : ℝ) * ‖a‖ ^ 8

def potentialRate (a v : R3) : ℝ := 7 * ‖a‖ ^ 6 * ⟪a, v⟫

def potentialGradient (a : R3) (D : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 (fun j ↦ potentialRate a (D j))

def longitudinalRate (a : R3) (D : Fin 3 → R3) : R3 :=
  ∑ j, a j • evenRadialRate 2 a (D j)

theorem hasDerivAt_potential {a : ℝ → R3} {v : R3} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun τ ↦ potential (a τ)) (potentialRate (a t) v) t := by
  have h := (ha.norm_sq.fun_pow 4).const_mul (7 / 8 : ℝ)
  simp only [← pow_mul, Nat.reduceMul] at h
  apply h.congr_deriv
  unfold potentialRate
  ring

theorem inner_evenRadialRate_two (a v : R3) :
    ⟪a, evenRadialRate 2 a v⟫ = potentialRate a v := by
  simp only [evenRadialRate, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat,
    inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, potentialRate]
  ring

theorem cross_curlJet_radial (a : R3) (D : Fin 3 → R3) :
    cross a (curlJet (fun j ↦ evenRadialRate 2 a (D j))) - potentialGradient a D =
      -longitudinalRate a D := by
  rw [cross_curlJet]
  simp only [inner_evenRadialRate_two, potentialGradient, longitudinalRate]
  abel

theorem cross_curlJet_sub_gradient (a : R3) (D E : Fin 3 → R3) :
    cross a (curlJet E) - potentialGradient a D =
      -longitudinalRate a D +
        cross a (curlJet (fun j ↦ E j - evenRadialRate 2 a (D j))) := by
  have he : curlJet (fun j ↦ E j - evenRadialRate 2 a (D j)) =
      curlJet E - curlJet (fun j ↦ evenRadialRate 2 a (D j)) := by
    ext i
    fin_cases i <;> simp [curlJet] <;> ring
  rw [he, cross_sub_right, ← cross_curlJet_radial a D]
  abel

theorem longitudinalRate_eq (a : R3) (D : Fin 3 → R3) :
    longitudinalRate a D = evenRadialRate 2 a (∑ j, a j • D j) := by
  simp only [longitudinalRate, Fin.sum_univ_three, evenRadialRate,
    inner_add_right, real_inner_smul_right]
  module

theorem longitudinalRate_eq_zero (a : R3) (D : Fin 3 → R3)
    (h : ∑ j, a j • D j = 0) : longitudinalRate a D = 0 := by
  rw [longitudinalRate_eq, h]
  simp [evenRadialRate]

/-- Tangential layered jets incur no longitudinal cost, even when their
normal derivative is large. -/
theorem longitudinalRate_layered (a n v : R3) (h : ⟪a, n⟫ = 0) :
    longitudinalRate a (fun j ↦ n j • v) = 0 := by
  apply longitudinalRate_eq_zero
  have he : (∑ j : Fin 3, a j • n j • v) = ⟪a, n⟫ • v := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three]
    module
  rw [he, h, zero_smul]

theorem norm_longitudinalRate_le (a : R3) (D : Fin 3 → R3) :
    ‖longitudinalRate a D‖ ≤ 7 * ‖a‖ ^ 6 * ‖∑ j, a j • D j‖ := by
  rw [longitudinalRate_eq]
  convert norm_evenRadialRate_le 2 a (∑ j, a j • D j) using 1
  norm_num

theorem norm_longitudinalRate_layered_le (a n v : R3) :
    ‖longitudinalRate a (fun j ↦ n j • v)‖ ≤
      7 * ‖a‖ ^ 6 * (|⟪a, n⟫| * ‖v‖) := by
  have he : (∑ j : Fin 3, a j • n j • v) = ⟪a, n⟫ • v := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three]
    module
  simpa only [he, norm_smul, Real.norm_eq_abs] using
    norm_longitudinalRate_le a (fun j ↦ n j • v)

theorem norm_cross_curlJet_sub_gradient_le (a : R3) (D E : Fin 3 → R3) :
    ‖cross a (curlJet E) - potentialGradient a D‖ ≤
      7 * ‖a‖ ^ 6 * ‖∑ j, a j • D j‖ +
        ‖a‖ * ‖curlJet (fun j ↦ E j - evenRadialRate 2 a (D j))‖ := by
  rw [cross_curlJet_sub_gradient]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [norm_neg] using norm_longitudinalRate_le a D)
    (norm_cross_le _ _))

/-- Incompressibility converts the longitudinal radial derivative into
angular jets only, without division by amplitude. -/
theorem longitudinalRate_eq_angularJet (a : R3) (D : Fin 3 → R3)
    (hdiv : ∑ j, D j j = 0) :
    longitudinalRate a D = ‖a‖ ^ 4 •
      ((∑ j, a j • angularJet a D j) - (7 * ∑ j, angularJet a D j j) • a) := by
  have ht : (∑ j, angularJet a D j j) = -(∑ j, a j * ⟪a, D j⟫) := by
    simp only [angularJet, Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [Fin.sum_univ_three] at hdiv
    linear_combination (‖a‖ ^ 2) * hdiv
  rw [ht, longitudinalRate_eq]
  simp only [angularJet, evenRadialRate, Fin.sum_univ_three, inner_add_right,
    real_inner_smul_right]
  module

theorem longitudinalRate_eq_zero_of_parallel (a : R3) (D : Fin 3 → R3)
    (hdiv : ∑ j, D j j = 0) (c : Fin 3 → ℝ) (h : ∀ j, D j = c j • a) :
    longitudinalRate a D = 0 := by
  rw [longitudinalRate_eq_angularJet a D hdiv, angularJet_eq_zero_of_parallel a D c h]
  simp

end Mettapedia.Analysis.OcticCurlCancellation
