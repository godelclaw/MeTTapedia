import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SquaredGapTiltWeight
import Mettapedia.Analysis.EuclideanOperatorCoordinates

/-!
# Collision-safe squared projector increments

The Euclidean coordinate increment of the weighted spectral projector is
paid by vorticity and strain increments, including at eigenvalue collisions.
The second term retains the vorticity at the second endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight

open PancakeSpectralProjectorRegularity
open Mettapedia.Analysis.EuclideanOperatorCoordinates

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem norm_coordinates_weightedProjector_sub_sq_le (gamma : ℝ) (hg : 0 < gamma)
    (A B : SymmetricStrain) (w v : R3) :
    ‖coordinates (weightedProjector gamma A w) - coordinates (weightedProjector gamma B v)‖ ^ 2 ≤
      6 * (‖w - v‖ / gamma) ^ 2 + 2400 * (‖v‖ * ‖A.1 - B.1‖ / gamma ^ 2) ^ 2 := by
  rw [← map_sub]
  have hc := norm_coordinates_sq_le (weightedProjector gamma A w - weightedProjector gamma B v)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hc
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (norm_weightedProjector_sub_le gamma hg A B w v) 2
  have hs := sq_nonneg (‖w - v‖ / gamma - 20 * ‖v‖ * ‖A.1 - B.1‖ / gamma ^ 2)
  simp only [div_eq_mul_inv] at hc hp hs ⊢
  nlinarith only [hc, hp, hs]

end Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight
