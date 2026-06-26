import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes energy-inequality transport canaries

Finite canaries for the energy-inequality transport gate in the averaged-equation
route.  The gate requires an energy-inequality transport witness and a finite
budget in which final energy plus accumulated dissipation fits under initial
energy plus the represented transport allowance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Finite audit input for a transported energy-inequality budget. -/
structure NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy : Nat
  finalEnergy : Nat
  accumulatedDissipation : Nat
  transportAllowance : Nat
  suppliesEnergyInequalityTransport : Bool
  suppliesFiniteEnergyL2Diagnostic : Bool
  endpointEnergyNonincreasing : Bool
  localEnergyInequalityChecked : Bool
  dissipationTermRecorded : Bool
deriving DecidableEq, Repr

namespace NavierEnergyInequalityTransportCanaryAudit

/-- Left side of the transported finite energy budget. -/
def budgetLeft
    (audit : NavierEnergyInequalityTransportCanaryAudit) : Nat :=
  audit.finalEnergy + audit.accumulatedDissipation

/-- Right side of the transported finite energy budget. -/
def budgetRight
    (audit : NavierEnergyInequalityTransportCanaryAudit) : Nat :=
  audit.initialEnergy + audit.transportAllowance

/-- Whether final energy plus dissipation fits under the transported budget. -/
def energyBudgetHolds
    (audit : NavierEnergyInequalityTransportCanaryAudit) : Bool :=
  audit.budgetLeft <= audit.budgetRight

/-- Finite gate for energy-inequality transport compatibility. -/
def clearsEnergyInequalityTransportGate
    (audit : NavierEnergyInequalityTransportCanaryAudit) : Bool :=
  audit.suppliesEnergyInequalityTransport &&
    audit.energyBudgetHolds

end NavierEnergyInequalityTransportCanaryAudit

/-- Positive canary: exact unforced budget with the transport witness. -/
def navierEnergyInequalityExactBudgetCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 10
  finalEnergy := 7
  accumulatedDissipation := 3
  transportAllowance := 0
  suppliesEnergyInequalityTransport := true
  suppliesFiniteEnergyL2Diagnostic := false
  endpointEnergyNonincreasing := true
  localEnergyInequalityChecked := true
  dissipationTermRecorded := true

/-- Positive canary: a represented transport allowance can close the budget. -/
def navierEnergyInequalityAllowanceBudgetCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 10
  finalEnergy := 12
  accumulatedDissipation := 2
  transportAllowance := 4
  suppliesEnergyInequalityTransport := true
  suppliesFiniteEnergyL2Diagnostic := false
  endpointEnergyNonincreasing := false
  localEnergyInequalityChecked := true
  dissipationTermRecorded := true

/-- Negative canary: a transport-witness label cannot repair budget failure. -/
def navierEnergyInequalityWitnessBudgetViolationCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 10
  finalEnergy := 9
  accumulatedDissipation := 3
  transportAllowance := 0
  suppliesEnergyInequalityTransport := true
  suppliesFiniteEnergyL2Diagnostic := false
  endpointEnergyNonincreasing := true
  localEnergyInequalityChecked := true
  dissipationTermRecorded := true

/-- Negative canary: endpoint nonincrease does not include dissipation. -/
def navierEnergyInequalityEndpointOnlyCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 10
  finalEnergy := 9
  accumulatedDissipation := 3
  transportAllowance := 0
  suppliesEnergyInequalityTransport := false
  suppliesFiniteEnergyL2Diagnostic := false
  endpointEnergyNonincreasing := true
  localEnergyInequalityChecked := false
  dissipationTermRecorded := false

/-- Negative canary: finite-energy L2 bookkeeping is not energy transport. -/
def navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 8
  finalEnergy := 6
  accumulatedDissipation := 2
  transportAllowance := 0
  suppliesEnergyInequalityTransport := false
  suppliesFiniteEnergyL2Diagnostic := true
  endpointEnergyNonincreasing := true
  localEnergyInequalityChecked := true
  dissipationTermRecorded := true

/-- Negative canary: a local flag does not replace transported global budget. -/
def navierEnergyInequalityLocalOnlyCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 5
  finalEnergy := 5
  accumulatedDissipation := 2
  transportAllowance := 0
  suppliesEnergyInequalityTransport := false
  suppliesFiniteEnergyL2Diagnostic := false
  endpointEnergyNonincreasing := true
  localEnergyInequalityChecked := true
  dissipationTermRecorded := true

/-- The current finite-energy/BKM route as an energy-transport canary. -/
def navierCurrentEnergyBKMRouteEnergyInequalityTransportCanaryAudit :
    NavierEnergyInequalityTransportCanaryAudit where
  initialEnergy := 0
  finalEnergy := 0
  accumulatedDissipation := 0
  transportAllowance := 0
  suppliesEnergyInequalityTransport := false
  suppliesFiniteEnergyL2Diagnostic := true
  endpointEnergyNonincreasing := false
  localEnergyInequalityChecked := false
  dissipationTermRecorded := false

theorem navierEnergyInequalityExactBudget_lab_positive_canary :
    navierEnergyInequalityExactBudgetCanaryAudit.budgetLeft =
        10 ∧
      navierEnergyInequalityExactBudgetCanaryAudit.budgetRight =
        10 ∧
      navierEnergyInequalityExactBudgetCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityExactBudgetCanaryAudit.clearsEnergyInequalityTransportGate =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierEnergyInequalityAllowanceBudget_lab_positive_canary :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierEnergyInequalityWitnessBudgetViolation_negative_canary :
    navierEnergyInequalityWitnessBudgetViolationCanaryAudit.suppliesEnergyInequalityTransport =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityWitnessBudgetViolationCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierEnergyInequalityEndpointOnly_negative_canary :
    navierEnergyInequalityEndpointOnlyCanaryAudit.endpointEnergyNonincreasing =
        true ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityEndpointOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem navierEnergyInequalityFiniteL2BudgetOnly_negative_canary :
    navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.energyBudgetHolds =
        true ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.suppliesEnergyInequalityTransport =
        false ∧
      navierEnergyInequalityFiniteL2BudgetOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierEnergyInequalityLocalOnly_negative_canary :
    navierEnergyInequalityLocalOnlyCanaryAudit.localEnergyInequalityChecked =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.dissipationTermRecorded =
        true ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.energyBudgetHolds =
        false ∧
      navierEnergyInequalityLocalOnlyCanaryAudit.clearsEnergyInequalityTransportGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierCurrentEnergyBKMRouteEnergyInequalityTransportCanary_obstruction :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierEnergyInequalityTransportCanaries_guardrails :
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
  exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩

end NavierStokes
end FluidDynamics
end Mettapedia
