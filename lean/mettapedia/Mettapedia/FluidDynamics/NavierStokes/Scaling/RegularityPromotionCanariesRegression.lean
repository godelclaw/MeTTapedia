import Mettapedia.FluidDynamics.NavierStokes.Scaling.RegularityPromotionCanaries

/-!
# Navier-Stokes regularity-promotion canary regressions

Regression aliases for the finite regularity-promotion layer canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem regularity_promotion_all_layers_canary_regression :
    navierRegularityPromotionAllLayersCanaryAudit.scalingVerdictLayerClears =
        true ∧
      navierRegularityPromotionAllLayersCanaryAudit.worldInterfaceLayerClears =
        true ∧
      navierRegularityPromotionAllLayersCanaryAudit.averagedEquationCompatibilityLayerClears =
        true ∧
      navierRegularityPromotionAllLayersCanaryAudit.clearsRegularityPromotionGate =
        true := by
  exact navierRegularityPromotionAllLayers_lab_positive_canary

theorem regularity_promotion_layer_only_canary_regression :
    navierRegularityPromotionScalingOnlyCanaryAudit.scalingVerdictLayerClears =
        true ∧
      navierRegularityPromotionScalingOnlyCanaryAudit.worldInterfaceLayerClears =
        false ∧
      navierRegularityPromotionScalingOnlyCanaryAudit.averagedEquationCompatibilityLayerClears =
        false ∧
      navierRegularityPromotionScalingOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.scalingVerdictLayerClears =
        false ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.worldInterfaceLayerClears =
        true ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.averagedEquationCompatibilityLayerClears =
        false ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.scalingVerdictLayerClears =
        false ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.worldInterfaceLayerClears =
        false ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.averagedEquationCompatibilityLayerClears =
        true ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.clearsRegularityPromotionGate =
        false := by
  exact navierRegularityPromotionLayerOnly_negative_canary

theorem regularity_promotion_layer_pairs_canary_regression :
    navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.scalingVerdictLayerClears =
        true ∧
      navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.worldInterfaceLayerClears =
        true ∧
      navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.averagedEquationCompatibilityLayerClears =
        false ∧
      navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.scalingVerdictLayerClears =
        true ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.worldInterfaceLayerClears =
        false ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.averagedEquationCompatibilityLayerClears =
        true ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.scalingVerdictLayerClears =
        false ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.worldInterfaceLayerClears =
        true ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.averagedEquationCompatibilityLayerClears =
        true ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.clearsRegularityPromotionGate =
        false := by
  exact navierRegularityPromotionLayerPairs_negative_canary

theorem current_energy_bkm_route_regularity_promotion_canary_obstruction_regression :
    navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.scalingVerdictLayerClears =
        false ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.worldInterfaceLayerClears =
        false ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.averagedEquationCompatibilityLayerClears =
        false ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.clearsRegularityPromotionGate =
        false := by
  exact navierCurrentEnergyBKMRouteRegularityPromotionCanary_obstruction

theorem regularity_promotion_layer_omissions_guardrails_regression :
    navierRegularityPromotionAllLayersCanaryAudit.clearsRegularityPromotionGate =
        true ∧
      navierRegularityPromotionScalingOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionAveragedEquationOnlyCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionScalingWorldsNoAveragedEquationCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionScalingAveragedEquationNoWorldsCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierRegularityPromotionWorldsAveragedEquationNoScalingCanaryAudit.clearsRegularityPromotionGate =
        false ∧
      navierCurrentEnergyBKMRouteRegularityPromotionCanaryAudit.clearsRegularityPromotionGate =
        false := by
  exact navierRegularityPromotionLayerOmissions_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
