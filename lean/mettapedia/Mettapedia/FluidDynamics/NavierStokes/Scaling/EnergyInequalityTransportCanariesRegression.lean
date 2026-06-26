import Mettapedia.FluidDynamics.NavierStokes.Scaling.EnergyInequalityTransportCanaries

/-!
# Navier-Stokes energy-inequality transport canary regressions

Regression aliases for the finite energy-inequality transport canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem energy_inequality_exact_budget_canary_regression :
    navierEnergyInequalityExactBudgetCanaryAudit.budgetLeft =
        10 ∧
      navierEnergyInequalityExactBudgetCanaryAudit.budgetRight =
        10 ∧
      navierEnergyInequalityExactBudgetCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityExactBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true := by
  exact navierEnergyInequalityExactBudget_lab_positive_canary

theorem energy_inequality_allowance_budget_canary_regression :
    navierEnergyInequalityAllowanceBudgetCanaryAudit.endpointEnergyNonincreasing =
        false ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.budgetLeft =
        14 ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.budgetRight =
        14 ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true := by
  exact navierEnergyInequalityAllowanceBudget_lab_positive_canary

theorem energy_inequality_witness_budget_violation_canary_regression :
    navierEnergyInequalityWitnessBudgetViolationCanaryAudit.suppliesEnergyInequalityTransport =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact navierEnergyInequalityWitnessBudgetViolation_negative_canary

theorem energy_inequality_endpoint_only_canary_regression :
    navierEnergyInequalityEndpointOnlyCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact navierEnergyInequalityEndpointOnly_negative_canary

theorem energy_inequality_finite_l2_budget_only_canary_regression :
    navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesEnergyInequalityTransport =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact navierEnergyInequalityFiniteL2BudgetOnly_negative_canary

theorem energy_inequality_local_only_canary_regression :
    navierEnergyInequalityLocalOnlyCanaryAudit.localEnergyInequalityChecked =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.dissipationTermRecorded =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact navierEnergyInequalityLocalOnly_negative_canary

theorem current_energy_bkm_route_energy_inequality_transport_canary_obstruction_regression :
    navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit.energyBudgetHolds =
        true ∧
      navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit.suppliesEnergyInequalityTransport =
        false ∧
      navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      NavierAveragedEquationObligation.energyInequalityCompatibility.requiredWorldInterface =
        .energyInequalityTransport := by
  exact navierCurrentEnergyBKMRouteEnergyInequalityTransportCanary_obstruction

theorem energy_inequality_transport_canaries_guardrails_regression :
    navierEnergyInequalityExactBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.endpointEnergyNonincreasing =
        false ∧
      navierEnergyInequalityAllowanceBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.suppliesEnergyInequalityTransport =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesEnergyInequalityTransport =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.localEnergyInequalityChecked =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact navierEnergyInequalityTransportCanaries_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
