import Mettapedia.Analysis.CrossProductEvolution

/-!
# Signed two-point angle rate and the strain-difference channel

The common-strain cancellation is explicit. The remaining pair forcing is
the strain difference acting across the pair, plus the two endpoint forces.
For vorticity these endpoint forces include viscosity, not just body forces.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanCrossProduct

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def pairForcing (S T : Op) (a b f g : R3) : R3 :=
  cross a ((T - S) b) + cross f b + cross a g

theorem cross_rate_eq (S T : Op) (a b f g : R3)
    (hc : cross (S a) b + cross a (S b) = -S (cross a b)) :
    cross (S a + f) b + cross a (T b + g) = -S (cross a b) + pairForcing S T a b f g := by
  have hT : T b = S b + (T - S) b := by simp
  calc
    _ = cross (S a) b + cross a (S b) + pairForcing S T a b f g := by
      rw [cross_add_left, cross_add_right, hT, cross_add_right]
      unfold pairForcing
      abel
    _ = _ := by rw [hc]

def angleRate (S T : Op) (a b f g : R3) : ℝ :=
  -2 * ⟪cross a b, S (cross a b)⟫ / (‖a‖ ^ 2 * ‖b‖ ^ 2) +
    2 * ⟪cross a b, pairForcing S T a b f g⟫ / (‖a‖ ^ 2 * ‖b‖ ^ 2) -
      2 * angleEnergy a b * (⟪a, S a + f⟫ / ‖a‖ ^ 2 + ⟪b, T b + g⟫ / ‖b‖ ^ 2)

/-- The signed contribution of strain variation and the two endpoint forces,
including their action on the normalization. -/
def anglePerturbation (S T : Op) (a b f g : R3) : ℝ :=
  2 * ⟪cross a b, pairForcing S T a b f g⟫ / (‖a‖ ^ 2 * ‖b‖ ^ 2) -
    2 * angleEnergy a b *
      (⟪a, f⟫ / ‖a‖ ^ 2 + (⟪b, (T - S) b⟫ + ⟪b, g⟫) / ‖b‖ ^ 2)

theorem angleRate_eq_common_add_perturbation (S T : Op) (a b f g : R3) :
    angleRate S T a b f g = angleRate S S a b 0 0 + anglePerturbation S T a b f g := by
  simp only [angleRate, anglePerturbation, pairForcing, sub_self, zero_apply,
    cross_zero, zero_cross, add_zero, inner_zero_right, mul_zero, zero_div,
    inner_add_right, sub_apply, inner_sub_right]
  ring

theorem hasDerivAt_cross_of_strainEquations {a b : ℝ → R3} {t : ℝ} (S T : Op) (f g : R3)
    (ha : HasDerivAt a (S (a t) + f) t) (hb : HasDerivAt b (T (b t) + g) t)
    (hc : cross (S (a t)) (b t) + cross (a t) (S (b t)) = -S (cross (a t) (b t))) :
    HasDerivAt (fun τ ↦ cross (a τ) (b τ))
      (-S (cross (a t) (b t)) + pairForcing S T (a t) (b t) f g) t := by
  simpa only [cross_rate_eq S T (a t) (b t) f g hc] using hasDerivAt_cross ha hb

theorem hasDerivAt_angleEnergy_of_strainEquations {a b : ℝ → R3} {t : ℝ} (S T : Op) (f g : R3)
    (ha : HasDerivAt a (S (a t) + f) t) (hb : HasDerivAt b (T (b t) + g) t)
    (ha0 : a t ≠ 0) (hb0 : b t ≠ 0)
    (hc : cross (S (a t)) (b t) + cross (a t) (S (b t)) = -S (cross (a t) (b t))) :
    HasDerivAt (fun τ ↦ angleEnergy (a τ) (b τ)) (angleRate S T (a t) (b t) f g) t := by
  have h := hasDerivAt_angleEnergy ha hb ha0 hb0
  apply h.congr_deriv
  rw [cross_rate_eq S T (a t) (b t) f g hc]
  simp only [angleRate, inner_add_right, inner_neg_right]
  ring

theorem angleRate_common_strain_unit (S : Op) (a b : R3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    angleRate S S a b 0 0 =
      -2 * (⟪cross a b, S (cross a b)⟫ +
        (⟪a, S a⟫ + ⟪b, S b⟫) * ‖cross a b‖ ^ 2) := by
  simp only [angleRate, pairForcing, sub_self, zero_apply, cross_zero, zero_cross, add_zero,
    inner_zero_right, mul_zero, angleEnergy, ha, hb, one_pow, one_mul, div_one]
  ring

end Mettapedia.Analysis.EuclideanCrossProduct
