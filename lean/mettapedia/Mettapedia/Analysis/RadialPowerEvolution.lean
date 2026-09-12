import Mettapedia.Analysis.RadialPower
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Exact derivatives of even radial powers, including at zero -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPower

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivative of the radial power with exponent `2*(n+1)`. -/
def evenRadialRate (n : ℕ) (a v : E) : E :=
  ‖a‖ ^ (2 * (n + 1)) • v +
    ((2 * (n + 1) : ℝ) * ‖a‖ ^ (2 * n) * ⟪a, v⟫) • a

theorem hasDerivAt_radialPower_even (n : ℕ) {a : ℝ → E} {v : E} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun τ ↦ radialPower (2 * (n + 1)) (a τ)) (evenRadialRate n (a t) v) t := by
  have h := ((ha.norm_sq).pow (n + 1)).smul ha
  change HasDerivAt (fun τ ↦ (‖a τ‖ ^ 2) ^ (n + 1) • a τ) _ t at h
  simp only [Pi.pow_apply, Nat.add_sub_cancel, ← pow_mul] at h
  unfold radialPower
  apply h.congr_deriv
  simp only [evenRadialRate, Nat.cast_add, Nat.cast_one]
  module

def radialStrainExcess (n : ℕ) (S : E →L[ℝ] E) (a : E) : E :=
  ((2 * (n + 1) : ℝ) * ‖a‖ ^ (2 * n) * ⟪a, S a⟫) • a

theorem radialStrainExcess_of_rayleigh (n : ℕ) (S : E →L[ℝ] E) (a : E) (α : ℝ)
    (ha : ⟪a, S a⟫ = α * ‖a‖ ^ 2) :
    radialStrainExcess n S a = ((2 * (n + 1) : ℝ) * α) • radialPower (2 * (n + 1)) a := by
  simp only [radialStrainExcess, ha, radialPower, smul_smul,
    show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  module

theorem evenRadialRate_strain_add (n : ℕ) (S : E →L[ℝ] E) (a f : E) :
    evenRadialRate n a (S a + f) =
      S (radialPower (2 * (n + 1)) a) + radialStrainExcess n S a + evenRadialRate n a f := by
  simp only [evenRadialRate, radialStrainExcess, radialPower, map_smul, inner_add_right]
  module

end Mettapedia.Analysis.RadialPower
