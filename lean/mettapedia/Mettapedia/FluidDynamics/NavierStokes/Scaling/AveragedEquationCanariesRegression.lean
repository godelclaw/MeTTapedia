import Mettapedia.FluidDynamics.NavierStokes.Scaling.AveragedEquationCanaries

/-!
# Navier-Stokes averaged-equation canary regressions

Regression aliases for the finite averaged-equation interface canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem averaged_equation_full_interface_canary_regression :
    navierAveragedEquationFullInterfaceCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationFullInterfaceCanaryAudit.challengeWorldInterfacesClear =
        true ∧
      navierAveragedEquationFullInterfaceCanaryAudit.missingObligations =
        [] ∧
      navierAveragedEquationFullInterfaceCanaryAudit.missingChallengeWorldInterfaces =
        [] ∧
      navierAveragedEquationFullInterfaceCanaryAudit.clearsAveragedEquationGate =
        true := by
  exact navierAveragedEquationFullInterface_lab_positive_canary

theorem averaged_equation_obligations_only_canary_regression :
    navierAveragedEquationObligationsOnlyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.missingChallengeWorldInterfaces =
        NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierAveragedEquationObligationsOnly_negative_canary

theorem averaged_equation_interfaces_only_canary_regression :
    navierAveragedEquationInterfacesOnlyCanaryAudit.representedAllRequiredObligations =
        false ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.challengeWorldInterfacesClear =
        true ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.missingObligations =
        currentNavierAveragedEquationCompatibilityObligations ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierAveragedEquationInterfacesOnly_negative_canary

theorem averaged_equation_obligation_interfaces_without_world_family_canary_regression :
    navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.missingChallengeWorldInterfaces =
        [ .averagedEquationWorldFamily ] ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierAveragedEquationObligationInterfacesWithoutWorldFamily_negative_canary

theorem averaged_momentum_only_canary_regression :
    navierAveragedMomentumOnlyCanaryAudit.representedAllRequiredObligations =
        false ∧
      navierAveragedMomentumOnlyCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierAveragedMomentumOnlyCanaryAudit.missingObligations =
        [ .reynoldsStressClosure
        , .energyInequalityCompatibility
        , .criticalScalingCompatibility
        ] ∧
      navierAveragedMomentumOnlyCanaryAudit.missingChallengeWorldInterfaces =
        [ .reynoldsStressClosureWitness
        , .energyInequalityTransport
        , .criticalScalingTransport
        ] ∧
      navierAveragedMomentumOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierAveragedMomentumOnly_negative_canary

theorem current_energy_bkm_route_averaged_equation_canary_obstruction_regression :
    navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.representedAllRequiredObligations =
        false ∧
      navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.missingObligations =
        currentNavierAveragedEquationCompatibilityObligations ∧
      navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.missingChallengeWorldInterfaces =
        NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces ∧
      navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierCurrentEnergyBKMRouteAveragedEquationCanary_obstruction

theorem averaged_equation_canaries_guardrails_regression :
    navierAveragedEquationFullInterfaceCanaryAudit.clearsAveragedEquationGate =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.challengeWorldInterfacesClear =
        true ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.missingChallengeWorldInterfaces =
        [ .averagedEquationWorldFamily ] ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.clearsAveragedEquationGate =
        false ∧
      navierAveragedMomentumOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact navierAveragedEquationCanaries_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
