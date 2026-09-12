import Mettapedia.Analysis.SignedCrossKernelEvolution
import Mettapedia.Analysis.HighAmplitudeWeightChainRule

/-!
# Algebraic channels of the signed high-amplitude material rate

Separate strain, moving-kernel transport and endpoint increments without
estimating any channel by its absolute value. At an amplitude tie these are
components of a fixed branch-selected rate, not separate chain rules for
three different paths. Their sum is the quantity identified by the full
material chain rule.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem highAmplitudeWeightRate_add (L : ℝ) (a b v w f g : R3) :
    highAmplitudeWeightRate L a b (v + f) (w + g) =
      highAmplitudeWeightRate L a b v w + highAmplitudeWeightRate L a b f g := by
  unfold highAmplitudeWeightRate
  split_ifs <;> simp only [inner_add_right, zero_add] <;> ring

theorem highAmplitudeWeightRate_smul (L c : ℝ) (a b f g : R3) :
    highAmplitudeWeightRate L a b (c • f) (c • g) = c * highAmplitudeWeightRate L a b f g := by
  unfold highAmplitudeWeightRate
  split_ifs <;> simp only [real_inner_smul_right, mul_zero] <;> ring

def pairedEndpointRate (n : ℕ) (H : Op) (a b f g : R3) : ℝ :=
  ⟪cross f b + cross a g, H (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b)⟫ +
    ⟪cross a b, H (evenRadialRate n a f - evenRadialRate n b g)⟫

theorem pairedEndpointRate_smul (n : ℕ) (H : Op) (c : ℝ) (a b f g : R3) :
    pairedEndpointRate n H a b (c • f) (c • g) = c * pairedEndpointRate n H a b f g := by
  have hr (v z : R3) : evenRadialRate n v (c • z) = c • evenRadialRate n v z := by
    simp only [evenRadialRate, real_inner_smul_right]
    module
  simp only [pairedEndpointRate, cross_smul_left, cross_smul_right, hr, ← smul_add,
    ← smul_sub, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem pairedEndpointRate_self (n : ℕ) (H : Op) (a b : R3) :
    pairedEndpointRate n H a b a b =
      ((2 * (n + 1) : ℝ) + 3) * pairedStretch (2 * (n + 1)) H a b := by
  have hr (v : R3) : evenRadialRate n v v =
      ((2 * (n + 1) : ℝ) + 1) • radialPower (2 * (n + 1)) v := by
    simp only [evenRadialRate, radialPower, real_inner_self_eq_norm_sq,
      show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    module
  simp only [pairedEndpointRate, pairedStretch, hr, ← smul_sub, map_smul,
    inner_add_left, real_inner_smul_right]
  ring

theorem pairedStretchRate_eq_strain_add_kernel_add_endpoint
    (n : ℕ) (S T H Hdot : Op) (a b f g : R3) :
    pairedStretchRate n S T H Hdot a b f g =
      pairedStretchRate n S T H 0 a b 0 0 +
        pairedStretch (2 * (n + 1)) Hdot a b + pairedEndpointRate n H a b f g := by
  simp only [pairedStretchRate, pairedStretch, pairedEndpointRate, symmetricPairForcing_eq,
    radialPairRemainder, evenRadialRate, cross_zero, zero_cross,
    inner_zero_right, mul_zero, smul_zero, zero_smul, add_zero,
    sub_zero, zero_add, add_apply, sub_apply, map_add, map_sub,
    inner_add_left, inner_add_right, inner_sub_right]
  ring

def highAmplitudeStrainRate (n : ℕ) (L : ℝ) (S T H : Op) (a b : R3) : ℝ :=
  highAmplitudeWeightRate L a b (S a) (T b) * pairedStretch (2 * (n + 1)) H a b +
    (1 - lowAmplitudeWeight L a b) * pairedStretchRate n S T H 0 a b 0 0

def highAmplitudeEndpointRate (n : ℕ) (L : ℝ) (H : Op) (a b f g : R3) : ℝ :=
  highAmplitudeWeightRate L a b f g * pairedStretch (2 * (n + 1)) H a b +
    (1 - lowAmplitudeWeight L a b) * pairedEndpointRate n H a b f g

theorem highAmplitudeRate_eq_strain_add_kernel_add_endpoint
    (n : ℕ) (L c : ℝ) (S T H Hdot : Op) (a b f g : R3) :
    highAmplitudeWeightRate L a b (S a + c • f) (T b + c • g) *
        pairedStretch (2 * (n + 1)) H a b +
      (1 - lowAmplitudeWeight L a b) * pairedStretchRate n S T H Hdot a b (c • f) (c • g) =
        highAmplitudeStrainRate n L S T H a b +
          highAmplitudeStretch (2 * (n + 1)) L Hdot a b +
            c * highAmplitudeEndpointRate n L H a b f g := by
  rw [highAmplitudeWeightRate_add, highAmplitudeWeightRate_smul,
    pairedStretchRate_eq_strain_add_kernel_add_endpoint, pairedEndpointRate_smul]
  unfold highAmplitudeStrainRate highAmplitudeStretch highAmplitudeEndpointRate
  ring

end Mettapedia.Analysis.SignedCrossKernel
