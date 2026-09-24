import Mettapedia.Analysis.SignedCrossKernel
import Mettapedia.Analysis.SymmetricCrossProductStrain
import Mettapedia.Analysis.RadialPowerEvolution
import Mettapedia.Analysis.OperatorQuadraticForm

/-!
# Signed radial cross-kernel evolution

Common strain cancels into a kernel commutator. Strain variation, radial
amplitude growth, endpoint forces and actual kernel transport remain
explicit. An angle-damping estimate is not a weighted-source budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def meanStrain (S T : Op) : Op := (1 / 2 : ℝ) • (S + T)

theorem meanStrain_self (S : Op) : meanStrain S S = S := by
  unfold meanStrain
  module

def radialPairRemainder (n : ℕ) (S T : Op) (a b f g : R3) : R3 :=
  (1 / 2 : ℝ) • ((S - T) (radialPower (2 * (n + 1)) a + radialPower (2 * (n + 1)) b)) +
    (radialStrainExcess n S a - radialStrainExcess n T b) +
    (evenRadialRate n a f - evenRadialRate n b g)

theorem radialPairRate_eq (n : ℕ) (S T : Op) (a b f g : R3) :
    evenRadialRate n a (S a + f) - evenRadialRate n b (T b + g) =
      meanStrain S T (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b) +
        radialPairRemainder n S T a b f g := by
  rw [evenRadialRate_strain_add, evenRadialRate_strain_add]
  simp only [meanStrain, radialPairRemainder, smul_apply, add_apply, sub_apply, map_sub, map_add]
  module

def pairedStretchRate (n : ℕ) (S T H Hdot : Op) (a b f g : R3) : ℝ :=
  ⟪cross a b, (Hdot + H * meanStrain S T - meanStrain S T * H)
    (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b)⟫ +
    ⟪symmetricPairForcing S T a b f g,
      H (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b)⟫ +
    ⟪cross a b, H (radialPairRemainder n S T a b f g)⟫

/-- A commuting kernel does not cancel radial amplification. -/
theorem pairedStretchRate_common_of_equal_rayleigh (n : ℕ) (S H : Op) (a b : R3) (α : ℝ)
    (hcomm : H * S = S * H)
    (ha : ⟪a, S a⟫ = α * ‖a‖ ^ 2) (hb : ⟪b, S b⟫ = α * ‖b‖ ^ 2) :
    pairedStretchRate n S S H 0 a b 0 0 =
      ((2 * (n + 1) : ℝ) * α) * pairedStretch (2 * (n + 1)) H a b := by
  simp only [pairedStretchRate, meanStrain_self, zero_add, hcomm, sub_self, zero_apply,
    inner_zero_right, zero_add, symmetricPairForcing_eq, cross_zero, zero_cross,
    smul_zero, add_zero, inner_zero_left, radialPairRemainder,
    radialStrainExcess_of_rayleigh n S a α ha, radialStrainExcess_of_rayleigh n S b α hb,
    evenRadialRate, inner_zero_right, mul_zero, smul_zero, zero_smul, zero_add]
  simp only [← smul_sub, map_smul, real_inner_smul_right, pairedStretch]

theorem hasDerivAt_pairedStretch (n : ℕ) {a b : ℝ → R3} {H : ℝ → Op} {t : ℝ}
    (S T Hdot : Op) (f g : R3)
    (ha : HasDerivAt a (S (a t) + f) t) (hb : HasDerivAt b (T (b t) + g) t)
    (hH : HasDerivAt H Hdot t)
    (hS : cross (S (a t)) (b t) + cross (a t) (S (b t)) = -S (cross (a t) (b t)))
    (hT : cross (T (b t)) (a t) + cross (b t) (T (a t)) = -T (cross (b t) (a t)))
    (hmean : ∀ v w : R3, ⟪meanStrain S T v, w⟫ = ⟪v, meanStrain S T w⟫) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1)) (H τ) (a τ) (b τ))
      (pairedStretchRate n S T (H t) Hdot (a t) (b t) f g) t := by
  have hc := hasDerivAt_cross ha hb
  have hr := (hasDerivAt_radialPower_even n ha).sub (hasDerivAt_radialPower_even n hb)
  have h := hc.inner ℝ (hH.clm_apply hr)
  apply h.congr_deriv
  rw [cross_rate_eq_symmetric _ _ _ _ _ _ hS hT, radialPairRate_eq]
  have hm (v : R3) : -(1 / 2 : ℝ) • (S v + T v) = -meanStrain S T v := by
    simp [meanStrain, neg_smul, add_comm]
  rw [hm]
  simp only [pairedStretchRate, inner_add_left, inner_neg_left, hmean, inner_add_right,
    inner_sub_right, add_apply, sub_apply, mul_apply_eq_comp, map_add, Pi.sub_apply]
  ring

end Mettapedia.Analysis.SignedCrossKernel
