import Mettapedia.Analysis.OddMapLineEstimate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionParity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltFreezing

/-!
# Unoriented direction freezing for the complete pressure tail

The finite-family estimate uses the actual weighted line distance, not
oriented vector closeness or the number of patches. Both inputs are full
continuous fields, and the direction-gain constant is uniform in scale.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionFreezing

open PressureHighInputAction PressureDirectionAction PressureDirectionParity SpectralTiltFreezing
open Mettapedia.Analysis.OddMapLineEstimate

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Field" => C(T3, C3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)

theorem exists_uniform_weighted_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ (ι : Type*) [Fintype ι], ∀ e : R3, ‖e‖ = 1 → ∀ r : ι → R3, (∀ i, ‖r i‖ = 1) →
      ∀ u v : Field, ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∀ x : T3,
      (∑ i, a i) * ‖tailOperator N hN J e u v x‖ ^ 2 ≤
        2 * (∑ i, a i * ‖tailOperator N hN J (r i) u v x‖ ^ 2) +
        2 * (C * (1 / 4 : ℝ) ^ J) ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 *
          ∑ i, a i * lineDistanceSq e (r i) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_field_bound
  refine ⟨C, hC, ?_⟩
  intro N hN J ι _ e he r hr u v a ha x
  let F : R3 → C3 := fun d ↦ tailOperator N hN J d u v x
  have ho (d : R3) : F (-d) = -F d := by
    simp only [F, tailOperator_neg]
    rfl
  have hl (d f : R3) (hd : ‖d‖ = 1) (hf : ‖f‖ = 1) :
      ‖F d - F f‖ ≤ ((C * (1 / 4 : ℝ) ^ J) * ‖u‖ * ‖v‖) * ‖d - f‖ :=
    (hb N hN J d f hd hf u v x).trans_eq (by ring)
  have h := sum_weight_mul_norm_sq_le F ho ((C * (1 / 4 : ℝ) ^ J) * ‖u‖ * ‖v‖) hl e he r hr a ha
  simpa only [F, lineDistanceSq, mul_pow, mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionFreezing
