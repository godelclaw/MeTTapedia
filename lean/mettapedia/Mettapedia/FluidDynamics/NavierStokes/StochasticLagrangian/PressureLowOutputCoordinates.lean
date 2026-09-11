import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CoherentPressurePair

/-!
# Quadratic pressure cancellation in input/output coordinates

Write the receiver frequency as `rho * q - k`, so the output is `rho * q`.
The pressure pair factors as `rho²` times a symbol with the output
direction evaluated at `q`. The identity includes `rho = 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates

open scoped RealInnerProductSpace
open Mettapedia.Analysis.EuclideanCrossProduct
open PressureTiltSymbol PancakeAnisotropyDepletion CoherentPressurePair

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def normalizedTrace (rho : ℝ) (k q w v : R3) : ℝ :=
  ⟪q, cross k w⟫ * ⟪q, cross (rho • q - k) v⟫ / (‖k‖ ^ 2 * ‖rho • q - k‖ ^ 2)

theorem tracePair_eq_lowOutput (rho : ℝ) (k q w v : R3) :
    tracePair k (rho • q - k) w v = rho ^ 2 * normalizedTrace rho k q w v := by
  have h1 : ⟪rho • q - k, cross k w⟫ = rho * ⟪q, cross k w⟫ := by
    rw [inner_sub_left, real_inner_smul_left, inner_self_cross, sub_zero]
  have h2 : ⟪k, cross (rho • q - k) v⟫ = rho * ⟪q, cross (rho • q - k) v⟫ := by
    have hz := inner_self_cross (rho • q - k) v
    rw [inner_sub_left, real_inner_smul_left] at hz
    linarith
  rw [tracePair, h1, h2, normalizedTrace]
  ring

theorem tiltSymbol_smul (e q : R3) (rho : ℝ) (hr : rho ≠ 0) :
    tiltSymbol e (rho • q) = tiltSymbol e q := by
  by_cases hq : q = 0
  · simp [hq, tiltSymbol_zero]
  · simp only [tiltSymbol, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, lineRemainder_smul, smul_smul]
    congr 1
    field_simp

theorem tiltPair_eq_lowOutput (e : R3) (rho : ℝ) (k q w v : R3) :
    tiltPair e k (rho • q - k) w v =
      rho ^ 2 • (normalizedTrace rho k q w v • tiltSymbol e q) := by
  by_cases hr : rho = 0
  · simp [hr, tiltPair, tiltSymbol_zero]
  · rw [tiltPair, show k + (rho • q - k) = rho • q by abel,
      tracePair_eq_lowOutput, tiltSymbol_smul e q rho hr,
      mul_smul]

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputCoordinates
