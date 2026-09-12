import Mettapedia.Analysis.RadialPowerEvolution

/-!
# Curvature of even radial powers

The index gives exponent `2 * (n + 2)`, so every norm power in the
curvature is nonnegative. The formula is polynomial and includes zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPower

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def evenRadialCurvature (n : ℕ) (a v : E) : E :=
  ((4 * (n + 2) : ℝ) * ‖a‖ ^ (2 * (n + 1)) * ⟪a, v⟫) • v +
    (((2 * (n + 2) : ℝ) * ‖a‖ ^ (2 * (n + 1)) * ‖v‖ ^ 2) +
      ((4 * (n + 2) * (n + 1) : ℝ) * ‖a‖ ^ (2 * n) * ⟪a, v⟫ ^ 2)) • a

theorem continuous_evenRadialRate {X : Type*} [TopologicalSpace X]
    (n : ℕ) {a v : X → E} (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x ↦ evenRadialRate n (a x) (v x)) := by
  unfold evenRadialRate
  fun_prop

theorem continuous_evenRadialCurvature {X : Type*} [TopologicalSpace X]
    (n : ℕ) {a v : X → E} (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x ↦ evenRadialCurvature n (a x) (v x)) := by
  unfold evenRadialCurvature
  fun_prop

theorem hasDerivAt_evenRadialRate (n : ℕ) {a v : ℝ → E} {z : E} {t : ℝ}
    (ha : HasDerivAt a (v t) t) (hv : HasDerivAt v z t) :
    HasDerivAt (fun τ ↦ evenRadialRate (n + 1) (a τ) (v τ))
      (evenRadialRate (n + 1) (a t) z + evenRadialCurvature n (a t) (v t)) t := by
  have hA := (ha.norm_sq).fun_pow (n + 2)
  have hB := (((ha.norm_sq).fun_pow (n + 1)).const_mul (2 * (n + 2) : ℝ)).mul (ha.inner ℝ hv)
  have h := (hA.smul hv).add (hB.smul ha)
  change HasDerivAt (fun τ ↦
    (‖a τ‖ ^ 2) ^ (n + 2) • v τ +
      ((2 * (n + 2) : ℝ) * (‖a τ‖ ^ 2) ^ (n + 1) * ⟪a τ, v τ⟫) • a τ) _ t at h
  simp only [← pow_mul] at h
  convert h using 1
  · funext τ
    simp only [evenRadialRate, show n + 1 + 1 = n + 2 by omega,
      Nat.cast_add, Nat.cast_one]
    module
  · simp only [evenRadialRate, evenRadialCurvature, Nat.add_sub_cancel,
      show n + 2 - 1 = n + 1 by omega, show n + 1 + 1 = n + 2 by omega,
      real_inner_self_eq_norm_sq, Pi.mul_apply,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    module

end Mettapedia.Analysis.RadialPower
