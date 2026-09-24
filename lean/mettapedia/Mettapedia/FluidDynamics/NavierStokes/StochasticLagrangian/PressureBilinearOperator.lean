import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressureMisalignment
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The pressure pair as a continuous complex-bilinear operator

The operator uses the original Euclidean coefficient norm on both inputs
and the output. Its norm is at most one for a unit frozen direction;
no coordinate-count constant is introduced by the representation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureBilinearOperator

open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open ComplexPressurePair ComplexPressureMisalignment

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def pressurePairLinear (e : R3) (k p : Wavevector) : C3 →ₗ[ℂ] C3 →ₗ[ℂ] C3 :=
  LinearMap.mk₂ ℂ (fun w v ↦ tiltPair e k p (WithLp.ofLp w) (WithLp.ofLp v))
    (fun w z v ↦ by simpa only [WithLp.ofLp_add] using tiltPair_add_left e k p _ _ _)
    (fun a w v ↦ by simpa only [WithLp.ofLp_smul] using tiltPair_smul_left a e k p _ _)
    (fun w v z ↦ by simpa only [WithLp.ofLp_add] using tiltPair_add_right e k p _ _ _)
    (fun a w v ↦ by simpa only [WithLp.ofLp_smul] using tiltPair_smul_right a e k p _ _)

theorem norm_pressurePairLinear_le (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : C3) :
    ‖pressurePairLinear e k p w v‖ ≤ 1 * ‖w‖ * ‖v‖ := by
  simpa only [pressurePairLinear, LinearMap.mk₂_apply, coefficientVec, WithLp.toLp_ofLp, one_mul] using
    norm_tiltPair_le e he k p (WithLp.ofLp w) (WithLp.ofLp v)

def pressurePairOperator (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) : C3 →L[ℂ] C3 →L[ℂ] C3 :=
  (pressurePairLinear e k p).mkContinuous₂ 1 (norm_pressurePairLinear_le e he k p)

theorem pressurePairOperator_apply (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : C3) :
    pressurePairOperator e he k p w v = tiltPair e k p (WithLp.ofLp w) (WithLp.ofLp v) := rfl

theorem norm_pressurePairOperator_le (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) :
    ‖pressurePairOperator e he k p‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end Mettapedia.FluidDynamics.NavierStokes.PressureBilinearOperator
