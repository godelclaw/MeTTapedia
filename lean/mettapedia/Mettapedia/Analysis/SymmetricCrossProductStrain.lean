import Mettapedia.Analysis.CrossProductStrain

/-! # Symmetric endpoint decomposition of the signed two-point angle rate -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

/-- Averaging the two endpoint decompositions preserves the signed strain
difference and both endpoint forces. -/
def symmetricPairForcing (S T : Op) (a b f g : R3) : R3 :=
  (1 / 2 : ℝ) • (pairForcing S T a b f g - pairForcing T S b a g f)

theorem symmetricPairForcing_eq (S T : Op) (a b f g : R3) :
    symmetricPairForcing S T a b f g =
      (1 / 2 : ℝ) • (cross a ((T - S) b) + cross ((S - T) a) b) +
        cross f b + cross a g := by
  unfold symmetricPairForcing pairForcing
  rw [cross_swap ((S - T) a) b, cross_swap a g, cross_swap f b]
  module

theorem cross_rate_eq_symmetric (S T : Op) (a b f g : R3)
    (hS : cross (S a) b + cross a (S b) = -S (cross a b))
    (hT : cross (T b) a + cross b (T a) = -T (cross b a)) :
    cross (S a + f) b + cross a (T b + g) =
      -(1 / 2 : ℝ) • (S (cross a b) + T (cross a b)) + symmetricPairForcing S T a b f g := by
  have h1 := cross_rate_eq S T a b f g hS
  have h2 : cross (S a + f) b + cross a (T b + g) =
      -T (cross a b) - pairForcing T S b a g f := by
    have h := congrArg Neg.neg (cross_rate_eq T S b a g f hT)
    simp only [cross_swap a (T b + g), cross_swap (S a + f) b,
      cross_swap a b, map_neg, neg_add, neg_neg] at h
    simpa only [sub_eq_add_neg, add_comm] using h
  calc
    _ = (1 / 2 : ℝ) • (cross (S a + f) b + cross a (T b + g)) +
        (1 / 2 : ℝ) • (cross (S a + f) b + cross a (T b + g)) := by module
    _ = (1 / 2 : ℝ) • (-S (cross a b) + pairForcing S T a b f g) +
        (1 / 2 : ℝ) • (-T (cross a b) - pairForcing T S b a g f) :=
      congrArg₂ (· + ·) (congrArg (fun v : R3 ↦ (1 / 2 : ℝ) • v) h1)
        (congrArg (fun v : R3 ↦ (1 / 2 : ℝ) • v) h2)
    _ = _ := by unfold symmetricPairForcing; module

def symmetricAnglePerturbation (S T : Op) (a b f g : R3) : ℝ :=
  2 * ⟪cross a b, symmetricPairForcing S T a b f g⟫ / (‖a‖ ^ 2 * ‖b‖ ^ 2) -
    2 * angleEnergy a b * (⟪a, f⟫ / ‖a‖ ^ 2 + ⟪b, g⟫ / ‖b‖ ^ 2)

def symmetricAngleRate (S T : Op) (a b f g : R3) : ℝ :=
  -(⟪cross a b, S (cross a b)⟫ + ⟪cross a b, T (cross a b)⟫) /
      (‖a‖ ^ 2 * ‖b‖ ^ 2) -
    2 * angleEnergy a b * (⟪a, S a⟫ / ‖a‖ ^ 2 + ⟪b, T b⟫ / ‖b‖ ^ 2) +
      symmetricAnglePerturbation S T a b f g

theorem angleRate_eq_symmetric (S T : Op) (a b f g : R3)
    (hS : cross (S a) b + cross a (S b) = -S (cross a b))
    (hT : cross (T b) a + cross b (T a) = -T (cross b a)) :
    angleRate S T a b f g = symmetricAngleRate S T a b f g := by
  have h := (cross_rate_eq S T a b f g hS).symm.trans
    (cross_rate_eq_symmetric S T a b f g hS hT)
  calc
    _ = 2 * ⟪cross a b, -S (cross a b) + pairForcing S T a b f g⟫ /
        (‖a‖ ^ 2 * ‖b‖ ^ 2) -
        2 * angleEnergy a b * (⟪a, S a + f⟫ / ‖a‖ ^ 2 + ⟪b, T b + g⟫ / ‖b‖ ^ 2) := by
      simp only [angleRate, inner_add_right, inner_neg_right]
      ring
    _ = _ := by
      rw [h]
      simp only [symmetricAngleRate, symmetricAnglePerturbation,
        inner_add_right, real_inner_smul_right]
      ring

theorem hasDerivAt_angleEnergy_symmetricStrain {a b : ℝ → R3} {t : ℝ} (S T : Op) (f g : R3)
    (ha : HasDerivAt a (S (a t) + f) t) (hb : HasDerivAt b (T (b t) + g) t)
    (ha0 : a t ≠ 0) (hb0 : b t ≠ 0)
    (hS : cross (S (a t)) (b t) + cross (a t) (S (b t)) = -S (cross (a t) (b t)))
    (hT : cross (T (b t)) (a t) + cross (b t) (T (a t)) = -T (cross (b t) (a t))) :
    HasDerivAt (fun τ ↦ angleEnergy (a τ) (b τ))
      (symmetricAngleRate S T (a t) (b t) f g) t := by
  apply (hasDerivAt_angleEnergy ha hb ha0 hb0).congr_deriv
  rw [cross_rate_eq_symmetric S T (a t) (b t) f g hS hT]
  simp only [symmetricAngleRate, symmetricAnglePerturbation, inner_add_right, real_inner_smul_right]
  ring

end Mettapedia.Analysis.EuclideanCrossProduct
