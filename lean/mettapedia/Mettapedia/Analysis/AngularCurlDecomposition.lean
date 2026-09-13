import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Polynomial angular part of a curl jet

For a vector `a` and its first jet `D`, removing each radial derivative
gives `|a|² D_j - <a,D_j> a`. Its curl differs from `|a|² curl D` by
the cross product of the amplitude gradient with `a`. The angular curl
therefore preserves the scaled helicity pairing and has a norm bound
using angular, not radial, dissipation. All formulas remain polynomial
at `a = 0`; no normalized direction field is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlDecomposition

open scoped RealInnerProductSpace Matrix
open WeightedCurlCancellation EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The first derivative of half the squared amplitude. -/
def amplitudeGradient (a : R3) (D : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 (fun j ↦ ⟪a, D j⟫)

/-- Squared-amplitude times the part of each derivative orthogonal to `a`. -/
def angularJet (a : R3) (D : Fin 3 → R3) (j : Fin 3) : R3 :=
  ‖a‖ ^ 2 • D j - ⟪a, D j⟫ • a

def angularCurl (a : R3) (D : Fin 3 → R3) : R3 := curlJet (angularJet a D)

def angularDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 6 * ∑ j : Fin 3, ‖D j‖ ^ 2 - ‖a‖ ^ 4 * ∑ j : Fin 3, ⟪a, D j⟫ ^ 2

def angularCurlDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 2 * ‖angularCurl a D‖ ^ 2

theorem inner_angularJet (a : R3) (D : Fin 3 → R3) (j : Fin 3) :
    ⟪a, angularJet a D j⟫ = 0 := by
  simp only [angularJet, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem angularJet_eq_zero_of_parallel (a : R3) (D : Fin 3 → R3) (c : Fin 3 → ℝ)
    (h : ∀ j, D j = c j • a) : angularJet a D = 0 := by
  funext j
  simp only [angularJet, h, real_inner_smul_right, real_inner_self_eq_norm_sq,
    smul_smul, mul_comm (‖a‖ ^ 2), sub_self, Pi.zero_apply]

theorem angularCurl_eq (a : R3) (D : Fin 3 → R3) :
    angularCurl a D = ‖a‖ ^ 2 • curlJet D - cross (amplitudeGradient a D) a := by
  ext i
  fin_cases i <;>
    simp [angularCurl, angularJet, curlJet, amplitudeGradient, cross, cross_apply,
      Matrix.cons_val_two] <;> ring

theorem inner_angularCurl (a : R3) (D : Fin 3 → R3) :
    ⟪a, angularCurl a D⟫ = ‖a‖ ^ 2 * ⟪a, curlJet D⟫ := by
  rw [angularCurl_eq, inner_sub_right, real_inner_smul_right, inner_cross_self, sub_zero]

theorem norm_angularJet_sq (a : R3) (D : Fin 3 → R3) (j : Fin 3) :
    ‖angularJet a D j‖ ^ 2 =
      ‖a‖ ^ 2 * (‖a‖ ^ 2 * ‖D j‖ ^ 2 - ⟪a, D j⟫ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [angularJet, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm (D j) a,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem weighted_sum_norm_angularJet_sq (a : R3) (D : Fin 3 → R3) :
    ‖a‖ ^ 2 * (∑ j : Fin 3, ‖angularJet a D j‖ ^ 2) = angularDensity a D := by
  simp only [norm_angularJet_sq, angularDensity, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_sub]
  simp only [Fin.sum_univ_three]
  ring

theorem angularDensity_nonneg (a : R3) (D : Fin 3 → R3) : 0 ≤ angularDensity a D := by
  rw [← weighted_sum_norm_angularJet_sq]
  positivity

theorem angularCurlDensity_nonneg (a : R3) (D : Fin 3 → R3) :
    0 ≤ angularCurlDensity a D := by unfold angularCurlDensity; positivity

theorem angularCurlDensity_le (a : R3) (D : Fin 3 → R3) :
    angularCurlDensity a D ≤ 2 * angularDensity a D := by
  have h := mul_le_mul_of_nonneg_left (norm_curlJet_sq_le (angularJet a D)) (sq_nonneg ‖a‖)
  calc
    _ ≤ ‖a‖ ^ 2 * (2 * ∑ j : Fin 3, ‖angularJet a D j‖ ^ 2) := h
    _ = 2 * angularDensity a D := by rw [← weighted_sum_norm_angularJet_sq]; ring

theorem angularCurlDensity_eq_zero_of_angularDensity_eq_zero (a : R3) (D : Fin 3 → R3)
    (h : angularDensity a D = 0) : angularCurlDensity a D = 0 := by
  have he := angularCurlDensity_le a D
  rw [h, mul_zero] at he
  exact le_antisymm he (angularCurlDensity_nonneg a D)

/-- Removing the amplitude curl does not remove the weighted helicity pairing. -/
theorem weighted_helicity_eq (a : R3) (D : Fin 3 → R3) (L : ℝ) :
    ‖a‖ ^ 4 * L * ⟪a, curlJet D⟫ = ‖a‖ ^ 2 * L * ⟪a, angularCurl a D⟫ := by
  rw [inner_angularCurl]
  ring

theorem continuous_angularCurl {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ angularCurl (a x) (fun j ↦ D j x)) := by
  have hJ (j : Fin 3) : Continuous (fun x ↦ angularJet (a x) (fun k ↦ D k x) j) :=
    ((ha.norm.pow 2).smul (hD j)).sub ((ha.inner (hD j)).smul ha)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact ((PiLp.continuous_apply 2 _ _).comp (hJ _)).sub
      ((PiLp.continuous_apply 2 _ _).comp (hJ _))

theorem continuous_angularCurlDensity {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ angularCurlDensity (a x) (fun j ↦ D j x)) :=
  (ha.norm.pow 2).mul ((continuous_angularCurl a D ha hD).norm.pow 2)

end Mettapedia.Analysis.AngularCurlDecomposition
