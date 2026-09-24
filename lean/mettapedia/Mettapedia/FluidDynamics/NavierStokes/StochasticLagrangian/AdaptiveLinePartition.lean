import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LineProjectorTilt
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAdaptiveStrainCover

/-!
# Adaptive partitions for continuous unoriented line fields

Only the rank-one projector is required to be continuous. Compactness
constructs a finite partition whose active cells have nearby lines;
the unit representatives may have arbitrary sign changes. This does not
assert continuity of a top eigenline at an eigenvalue collision.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AdaptiveLinePartition

open SpectralTiltFreezing PancakeAdaptiveStrainCover

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem exists_partition_of_continuous_projector (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho : ℝ) (hr : 0 < rho) :
    ∃ (centers : Finset T3) (weight : PartitionOfUnity (↑centers) T3),
      ∀ (center : ↑centers) (x : T3), weight center x ≠ 0 →
        lineDistanceSq (e x) (e center.1) ≤ rho ^ 2 := by
  obtain ⟨centers, weight, _, hactive⟩ := exists_finite_adaptive_spatial_strain_partition
    (fun x ↦ InnerProductSpace.rankOne ℝ (e x) (e x)) hP (by positivity : 0 < rho / 2)
  refine ⟨centers, weight, ?_⟩
  intro center x hx
  have h := lineDistanceSq_le_two_mul_projector_sub_sq (e x) (e center.1) (he x) (he center.1)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hactive center x hx).le 2
  nlinarith only [h, hs, sq_nonneg rho]

end Mettapedia.FluidDynamics.NavierStokes.AdaptiveLinePartition
