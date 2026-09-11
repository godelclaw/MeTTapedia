import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SmoothedPressureL2Budget

/-!
# Exact balance of smoothing and commutator costs

Completing the square gives the smallest possible displayed derivative
coefficient. Taking the smoothing parameter to zero cannot discard the
commutator cost. The optimum is attained when the potential norm and
pressure size are positive; no claim about the angular tail is made.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance

open PeriodicFourierTriad LocalPressureEllipticBudget PressurePatchSmoothing SmoothedPressureL2Budget

def pressureSizeSq (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  ‖pressureField chi K u‖ ^ 2 + 4 * eta ^ 2 * ‖traceField chi K u‖ ^ 2

theorem pressureSizeSq_nonneg (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : 0 ≤ pressureSizeSq eta chi K u := by
  unfold pressureSizeSq
  positivity

def balancedDerivativeCost (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  1536 * potentialCoordinateBound chi K u ^ 2 +
    24 * ‖potentialField chi K u‖ * Real.sqrt (pressureSizeSq eta chi K u)

def balancingParameter (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  6 * ‖potentialField chi K u‖ / Real.sqrt (pressureSizeSq eta chi K u)

theorem derivativeCost_eq_balanced_add_square (epsilon eta : ℝ) (he : epsilon ≠ 0)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) :
    derivativeCost epsilon eta chi K u = balancedDerivativeCost eta chi K u +
      2 / epsilon * (6 * ‖potentialField chi K u‖ -
        epsilon * Real.sqrt (pressureSizeSq eta chi K u)) ^ 2 := by
  have hid (A s : ℝ) : 72 / epsilon * A ^ 2 + 2 * epsilon * s ^ 2 =
      24 * A * s + 2 / epsilon * (6 * A - epsilon * s) ^ 2 := by
    field_simp
    ring
  have h := hid ‖potentialField chi K u‖ (Real.sqrt (pressureSizeSq eta chi K u))
  rw [Real.sq_sqrt (pressureSizeSq_nonneg eta chi K u)] at h
  unfold pressureSizeSq at h
  unfold derivativeCost balancedDerivativeCost pressureSizeSq
  nlinarith only [h]

theorem balancedDerivativeCost_le (epsilon eta : ℝ) (he : 0 < epsilon)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) :
    balancedDerivativeCost eta chi K u ≤ derivativeCost epsilon eta chi K u := by
  rw [derivativeCost_eq_balanced_add_square epsilon eta he.ne' chi K u]
  exact le_add_of_nonneg_right (by positivity)

theorem balancingParameter_pos (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) (hp : 0 < ‖potentialField chi K u‖)
    (hQ : 0 < pressureSizeSq eta chi K u) : 0 < balancingParameter eta chi K u := by
  exact div_pos (mul_pos (by norm_num) hp) (Real.sqrt_pos.mpr hQ)

theorem derivativeCost_balancingParameter (eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) (hp : 0 < ‖potentialField chi K u‖)
    (hQ : 0 < pressureSizeSq eta chi K u) :
    derivativeCost (balancingParameter eta chi K u) eta chi K u =
      balancedDerivativeCost eta chi K u := by
  rw [derivativeCost_eq_balanced_add_square _ eta (balancingParameter_pos eta chi K u hp hQ).ne' chi K u]
  have hcancel : balancingParameter eta chi K u * Real.sqrt (pressureSizeSq eta chi K u) =
      6 * ‖potentialField chi K u‖ :=
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr hQ).ne'
  rw [hcancel, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]

end Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingBalance
