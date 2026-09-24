import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalViscousFluxFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityNegation

/-!
# Velocity-sign reversal and the joint active-flux cost

The inviscid flux is odd and the viscous flux is even in the velocity.
The parallelogram identity therefore makes their separate squared costs
equal to the mean joint cost at the two signs. A uniform initial-data
argument cannot assume strict destructive interference at both signs.
No relation between the two subsequent viscous solution trajectories is
asserted by these snapshot identities.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalFluxParity

open scoped RealInnerProductSpace
open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeDyadicDirectionEvolution FullLambVector LocalVorticityNegation
open LongitudinalVorticityTime LongitudinalGradientFlux LongitudinalViscousFluxFourier

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem realField_neg (u : FourierVelocity) : realField (-u) = -realField u := by
  simp only [realField, fullFourierField_neg, map_neg]

theorem vorticityField_neg (u : FourierVelocity) : vorticityField (-u) = -vorticityField u := by
  simp only [vorticityField, fourierCurl_neg, realField_neg]

theorem velocityJet_neg (u : FourierVelocity) (j : Fin 3) (x : T3) :
    velocityJet (-u) j x = -velocityJet u j x := by
  have he : indexedDerivativeCoeff id j (-u) = -indexedDerivativeCoeff id j u := by
    funext q
    simp only [indexedDerivativeCoeff, Pi.neg_apply, smul_neg]
  simp only [velocityJet, he, fullFourierField_neg, ContinuousMap.neg_apply, map_neg]

theorem inviscid_fluxField_neg (u : FourierVelocity) : fluxField 0 (-u) = -fluxField 0 u := by
  funext j
  ext x
  simp only [fluxField, ContinuousMap.coe_mk, vorticityField_neg, ContinuousMap.neg_apply,
    PiLp.neg_apply, velocityJet_neg, neg_smul, smul_neg, neg_neg, mul_zero, zero_smul, add_zero,
    Pi.neg_apply]

theorem viscousFluxField_neg (u : FourierVelocity) : viscousFluxField (-u) = viscousFluxField u := by
  funext j
  ext x
  simp only [viscousFluxField_apply, fullCurlGradient_neg, PiLp.neg_apply, neg_smul, smul_neg, neg_neg]

theorem projectedFlux_inviscid_neg (u : FourierVelocity) : projectedFlux 0 (-u) = -projectedFlux 0 u := by
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (fluxField 0 (-u)) = _
  rw [inviscid_fluxField_neg, map_neg]
  rfl

theorem projectedFlux_neg (ν : ℝ) (u : FourierVelocity) :
    projectedFlux ν (-u) = -projectedFlux 0 u +
      (2 * ν) • gradientProjection (toTensorL2 (viscousFluxField u)) := by
  rw [projectedFlux_eq_inviscid_add_viscous, projectedFlux_inviscid_neg, viscousFluxField_neg]

theorem projectedFluxSquare_add_neg (ν : ℝ) (u : FourierVelocity) :
    projectedFluxSquare ν u + projectedFluxSquare ν (-u) =
      2 * (‖projectedFlux 0 u‖ ^ 2 +
        4 * ν ^ 2 * ‖gradientProjection (toTensorL2 (viscousFluxField u))‖ ^ 2) := by
  rw [projectedFluxSquare, projectedFluxSquare, projectedFlux_neg,
    projectedFlux_eq_inviscid_add_viscous]
  have h := parallelogram_law_with_norm ℝ
    ((2 * ν) • gradientProjection (toTensorL2 (viscousFluxField u))) (projectedFlux 0 u)
  rw [add_comm ((2 * ν) • _) _, sub_eq_add_neg, add_comm ((2 * ν) • _) _] at h
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
  nlinarith

theorem separate_cost_le_at_one_sign (ν : ℝ) (u : FourierVelocity) :
    (‖projectedFlux 0 u‖ ^ 2 + 4 * ν ^ 2 * ‖gradientProjection (toTensorL2 (viscousFluxField u))‖ ^ 2 ≤
      projectedFluxSquare ν u) ∨
    (‖projectedFlux 0 u‖ ^ 2 + 4 * ν ^ 2 * ‖gradientProjection (toTensorL2 (viscousFluxField u))‖ ^ 2 ≤
      projectedFluxSquare ν (-u)) := by
  have h := projectedFluxSquare_add_neg ν u
  by_cases hle : ‖projectedFlux 0 u‖ ^ 2 +
      4 * ν ^ 2 * ‖gradientProjection (toTensorL2 (viscousFluxField u))‖ ^ 2 ≤ projectedFluxSquare ν u
  · exact Or.inl hle
  · exact Or.inr (by linarith)

theorem separate_cost_le_of_both_sign_bounds (ν C : ℝ) (u : FourierVelocity)
    (hp : projectedFluxSquare ν u ≤ C) (hn : projectedFluxSquare ν (-u) ≤ C) :
    ‖projectedFlux 0 u‖ ^ 2 + 4 * ν ^ 2 * ‖gradientProjection (toTensorL2 (viscousFluxField u))‖ ^ 2 ≤ C := by
  linarith [projectedFluxSquare_add_neg ν u]

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalFluxParity
