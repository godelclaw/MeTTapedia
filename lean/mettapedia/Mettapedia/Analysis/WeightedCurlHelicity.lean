import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Radial absorption of the weighted curl defect

The helicity of a first jet is unchanged by adding arbitrary radial
derivatives. Young's inequality pays the longitudinal factor from radial
dissipation, leaving an explicit weighted helicity square. No bound on that
remaining square, or on its time integral, is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.WeightedCurlHelicity

open WeightedCurlCancellation
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def helicity (a : R3) (D : Fin 3 → R3) : ℝ := ⟪a, curlJet D⟫

/-- Radial amplitude derivatives make no contribution to curl helicity. -/
theorem helicity_add_radial (a : R3) (D : Fin 3 → R3) (b : Fin 3 → ℝ) :
    helicity a (fun j ↦ D j + b j • a) = helicity a D := by
  simp [helicity, curlJet, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three]
  ring

theorem helicity_radial (a : R3) (b : Fin 3 → ℝ) :
    helicity a (fun j ↦ b j • a) = 0 := by
  simpa [helicity, curlJet, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three] using helicity_add_radial a (fun _ ↦ 0) b

def longitudinalDefect (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 4 * (∑ j : Fin 3, a j * ⟪a, D j⟫) * helicity a D

def radialDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 4 * ∑ j : Fin 3, ⟪a, D j⟫ ^ 2

def helicityDensity (a : R3) (D : Fin 3 → R3) : ℝ :=
  ‖a‖ ^ 6 * helicity a D ^ 2

theorem abs_mul_le_weighted_sq (x y η : ℝ) (hη : 0 < η) :
    |x * y| ≤ η * x ^ 2 + y ^ 2 / (4 * η) := by
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * η by positivity)).mp
  have he : (η * x ^ 2 + y ^ 2 / (4 * η)) * (4 * η) =
      (4 * η) * η * x ^ 2 + y ^ 2 := by field_simp
  rw [he, abs_mul]
  have hs := sq_nonneg (2 * η * |x| - |y|)
  simp only [sub_sq, mul_pow, sq_abs] at hs
  nlinarith only [hs]

/-- The paid term is the radial part already present in the eighth-moment
vorticity identity. The remaining helicity square has an extra amplitude
weight and is not automatically paid by ordinary weighted palinstrophy. -/
theorem abs_longitudinalDefect_le (a : R3) (D : Fin 3 → R3)
    (η : ℝ) (hη : 0 < η) :
    |longitudinalDefect a D| ≤ η * radialDensity a D + helicityDensity a D / (4 * η) := by
  have hp (j : Fin 3) := abs_mul_le_weighted_sq
    (‖a‖ ^ 2 * ⟪a, D j⟫) (‖a‖ ^ 2 * a j * helicity a D) η hη
  have he : longitudinalDefect a D =
      ∑ j : Fin 3, (‖a‖ ^ 2 * ⟪a, D j⟫) * (‖a‖ ^ 2 * a j * helicity a D) := by
    simp only [longitudinalDefect, Fin.sum_univ_three]
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _ ↦ hp j)).trans_eq
  have ha : (∑ j : Fin 3, (a j) ^ 2) = ‖a‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
  simp only [radialDensity, helicityDensity, Fin.sum_univ_three] at ha ⊢
  field_simp
  linear_combination ‖a‖ ^ 4 * helicity a D ^ 2 * ha

theorem continuous_helicity {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ helicity (a x) (fun j ↦ D j x)) := by
  apply ha.inner
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact ((PiLp.continuous_apply 2 _ _).comp (hD _)).sub
      ((PiLp.continuous_apply 2 _ _).comp (hD _))

theorem continuous_longitudinalDefect {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ longitudinalDefect (a x) (fun j ↦ D j x)) :=
  ((ha.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
    ((PiLp.continuous_apply 2 _ j).comp ha).mul (ha.inner (hD j))))).mul
      (continuous_helicity a D ha hD)

theorem continuous_helicityDensity {X : Type*} [TopologicalSpace X]
    (a : X → R3) (D : Fin 3 → X → R3) (ha : Continuous a)
    (hD : ∀ j, Continuous (D j)) :
    Continuous (fun x ↦ helicityDensity (a x) (fun j ↦ D j x)) :=
  (ha.norm.pow 6).mul ((continuous_helicity a D ha hD).pow 2)

end Mettapedia.Analysis.WeightedCurlHelicity
