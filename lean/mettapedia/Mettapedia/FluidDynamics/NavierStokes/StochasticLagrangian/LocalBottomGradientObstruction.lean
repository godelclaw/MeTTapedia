import Mettapedia.Analysis.KernelCrossTerm
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralBounds

/-!
# An unpaid transverse channel in the bottom-energy gradient cross term

When an actual spatial projector derivative moves the bottom component
of a vector nontrivially, its cross term cannot be bounded for arbitrary
vector gradients by the bottom-projected gradient square and a fixed
constant alone. This rules out that pointwise absorption rule, not a
Navier–Stokes solution or a coupled or integrated cancellation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomGradientObstruction

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralProjectorRegularity
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeEigenframePerturbation
open PancakeMaterialProjectorTangent RankOneProjectorTangent BottomProjectorMotion
open LocalBottomEnergyDiffusion LocalSpatialSpectralBounds

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem not_exists_projectedGradient_bound (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) (w : R3)
    (hz : projectorFirst chi modes u j x
      (bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x) w) ≠ 0) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) x)
    ¬ ∃ A B : ℝ, ∀ v : R3,
      -4 * ⟪v, projectorFirst chi modes u j x w⟫ ≤ A * ‖P v‖ ^ 2 + B := by
  let S := spatialStrain modes (filteredVelocity chi u) x
  let P : Op := bottomEigenlineProjector S
  let D := projectorFirst chi modes u j x
  let z := D (P w)
  have ht : D * P + P * D = D := projectorFirst_tangent chi modes u j x hg
  have hp : P * P = P := lineProjector_mul_self _ (bottomVector_norm S)
  have hk : P z = 0 := projector_tangent_diagonal_zero P D hp ht w
  have hs : IsSelfAdjoint P := lineProjector_isSelfAdjoint (bottomVector S)
  have hi : ⟪z, P (D w)⟫ = 0 := by
    have hi' : ⟪P z, D w⟫ = ⟪z, P (D w)⟫ := hs.isSymmetric z (D w)
    rw [hk, inner_zero_left] at hi'
    exact hi'.symm
  have he := congrArg (fun A : Op ↦ A w) ht
  change z + P (D w) = D w at he
  have hzinner : ⟪z, D w⟫ = ‖z‖ ^ 2 := by
    rw [← he, inner_add_right, hi, add_zero, real_inner_self_eq_norm_sq]
  exact Mettapedia.Analysis.KernelCrossTerm.not_exists_projectedSquare_bound P z (D w) hk
    (by rw [hzinner]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomGradientObstruction
