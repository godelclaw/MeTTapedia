import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes averaged-equation canaries

Finite canaries for the averaged-equation compatibility layer.  They keep the
represented-obligation ledger separate from the challenge-world interface
ledger, because either layer alone is insufficient for route promotion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Finite audit input for averaged-equation compatibility canaries. -/
structure NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation : Bool
  representsReynoldsStressClosure : Bool
  representsEnergyInequalityCompatibility : Bool
  representsCriticalScalingCompatibility : Bool
  suppliesFiniteEnergyL2Diagnostic : Bool
  suppliesAveragedEquationWorldFamily : Bool
  suppliesAveragedMomentumWitness : Bool
  suppliesReynoldsStressClosureWitness : Bool
  suppliesEnergyInequalityTransport : Bool
  suppliesCriticalScalingTransport : Bool
deriving DecidableEq, Repr

namespace NavierAveragedEquationCanaryAudit

/-- Represented averaged-equation obligations reconstructed from Boolean flags. -/
def representedObligations
    (audit : NavierAveragedEquationCanaryAudit) :
    List NavierAveragedEquationObligation :=
  (if audit.representsAveragedMomentumEquation then
      [ .averagedMomentumEquation ]
    else
      []) ++
    (if audit.representsReynoldsStressClosure then
      [ .reynoldsStressClosure ]
    else
      []) ++
    (if audit.representsEnergyInequalityCompatibility then
      [ .energyInequalityCompatibility ]
    else
      []) ++
    if audit.representsCriticalScalingCompatibility then
      [ .criticalScalingCompatibility ]
    else
      []

/-- Supplied scaling-world interfaces reconstructed from Boolean flags. -/
def suppliedInterfaces
    (audit : NavierAveragedEquationCanaryAudit) :
    List NavierScalingWorldInterface :=
  (if audit.suppliesFiniteEnergyL2Diagnostic then
      [ .finiteEnergyL2Diagnostic ]
    else
      []) ++
    (if audit.suppliesAveragedEquationWorldFamily then
      [ .averagedEquationWorldFamily ]
    else
      []) ++
    (if audit.suppliesAveragedMomentumWitness then
      [ .averagedMomentumWitness ]
    else
      []) ++
    (if audit.suppliesReynoldsStressClosureWitness then
      [ .reynoldsStressClosureWitness ]
    else
      []) ++
    (if audit.suppliesEnergyInequalityTransport then
      [ .energyInequalityTransport ]
    else
      []) ++
    if audit.suppliesCriticalScalingTransport then
      [ .criticalScalingTransport ]
    else
      []

/-- Obligation status induced by the finite canary input. -/
def obligationStatus
    (audit : NavierAveragedEquationCanaryAudit) :
    NavierAveragedEquationCompatibilityStatus where
  routeKey := "navier.averaged-equation-canary"
  required := currentNavierAveragedEquationCompatibilityObligations
  represented := audit.representedObligations

/-- Challenge-world interface status induced by the finite canary input. -/
def worldInterfaces
    (audit : NavierAveragedEquationCanaryAudit) :
    NavierScalingRouteWorldInterfaces where
  routeKey := "navier.averaged-equation-canary"
  supplied := audit.suppliedInterfaces

/-- Whether all current averaged-equation obligations are represented. -/
def representedAllRequiredObligations
    (audit : NavierAveragedEquationCanaryAudit) : Bool :=
  audit.representsAveragedMomentumEquation &&
    audit.representsReynoldsStressClosure &&
    audit.representsEnergyInequalityCompatibility &&
    audit.representsCriticalScalingCompatibility

/-- Missing averaged-equation obligations for the finite canary. -/
def missingObligations
    (audit : NavierAveragedEquationCanaryAudit) :
    List NavierAveragedEquationObligation :=
  (if audit.representsAveragedMomentumEquation then
      []
    else
      [ .averagedMomentumEquation ]) ++
    (if audit.representsReynoldsStressClosure then
      []
    else
      [ .reynoldsStressClosure ]) ++
    (if audit.representsEnergyInequalityCompatibility then
      []
    else
      [ .energyInequalityCompatibility ]) ++
    if audit.representsCriticalScalingCompatibility then
      []
    else
      [ .criticalScalingCompatibility ]

/-- Whether the averaged-equation challenge-world interfaces are supplied. -/
def challengeWorldInterfacesClear
    (audit : NavierAveragedEquationCanaryAudit) : Bool :=
  audit.suppliesAveragedEquationWorldFamily &&
    audit.suppliesAveragedMomentumWitness &&
    audit.suppliesReynoldsStressClosureWitness &&
    audit.suppliesEnergyInequalityTransport &&
    audit.suppliesCriticalScalingTransport

/-- Missing averaged-equation challenge-world interfaces for the finite canary. -/
def missingChallengeWorldInterfaces
    (audit : NavierAveragedEquationCanaryAudit) :
    List NavierScalingWorldInterface :=
  (if audit.suppliesAveragedEquationWorldFamily then
      []
    else
      [ .averagedEquationWorldFamily ]) ++
    (if audit.suppliesAveragedMomentumWitness then
      []
    else
      [ .averagedMomentumWitness ]) ++
    (if audit.suppliesReynoldsStressClosureWitness then
      []
    else
      [ .reynoldsStressClosureWitness ]) ++
    (if audit.suppliesEnergyInequalityTransport then
      []
    else
      [ .energyInequalityTransport ]) ++
    if audit.suppliesCriticalScalingTransport then
      []
    else
      [ .criticalScalingTransport ]

/-- Two-layer finite gate for averaged-equation compatibility canaries. -/
def clearsAveragedEquationGate
    (audit : NavierAveragedEquationCanaryAudit) : Bool :=
  audit.representedAllRequiredObligations &&
    audit.challengeWorldInterfacesClear

end NavierAveragedEquationCanaryAudit

/-- Positive canary: all averaged-equation obligations and interfaces are present. -/
def navierAveragedEquationFullInterfaceCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := true
  representsReynoldsStressClosure := true
  representsEnergyInequalityCompatibility := true
  representsCriticalScalingCompatibility := true
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  suppliesReynoldsStressClosureWitness := true
  suppliesEnergyInequalityTransport := true
  suppliesCriticalScalingTransport := true

/-- Negative canary: obligations represented without challenge-world interfaces. -/
def navierAveragedEquationObligationsOnlyCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := true
  representsReynoldsStressClosure := true
  representsEnergyInequalityCompatibility := true
  representsCriticalScalingCompatibility := true
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesAveragedEquationWorldFamily := false
  suppliesAveragedMomentumWitness := false
  suppliesReynoldsStressClosureWitness := false
  suppliesEnergyInequalityTransport := false
  suppliesCriticalScalingTransport := false

/-- Negative canary: interfaces supplied without represented obligations. -/
def navierAveragedEquationInterfacesOnlyCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := false
  representsReynoldsStressClosure := false
  representsEnergyInequalityCompatibility := false
  representsCriticalScalingCompatibility := false
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  suppliesReynoldsStressClosureWitness := true
  suppliesEnergyInequalityTransport := true
  suppliesCriticalScalingTransport := true

/-- Negative canary: obligation witnesses without the averaged-equation world family. -/
def navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := true
  representsReynoldsStressClosure := true
  representsEnergyInequalityCompatibility := true
  representsCriticalScalingCompatibility := true
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesAveragedEquationWorldFamily := false
  suppliesAveragedMomentumWitness := true
  suppliesReynoldsStressClosureWitness := true
  suppliesEnergyInequalityTransport := true
  suppliesCriticalScalingTransport := true

/-- Negative canary: averaged momentum and its witness do not clear the full gate. -/
def navierAveragedMomentumOnlyCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := true
  representsReynoldsStressClosure := false
  representsEnergyInequalityCompatibility := false
  representsCriticalScalingCompatibility := false
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  suppliesReynoldsStressClosureWitness := false
  suppliesEnergyInequalityTransport := false
  suppliesCriticalScalingTransport := false

/-- The current finite-energy/BKM route as an averaged-equation canary. -/
def navierCurrentEnergyBKMRouteAveragedEquationCanaryAudit :
    NavierAveragedEquationCanaryAudit where
  representsAveragedMomentumEquation := false
  representsReynoldsStressClosure := false
  representsEnergyInequalityCompatibility := false
  representsCriticalScalingCompatibility := false
  suppliesFiniteEnergyL2Diagnostic := true
  suppliesAveragedEquationWorldFamily := false
  suppliesAveragedMomentumWitness := false
  suppliesReynoldsStressClosureWitness := false
  suppliesEnergyInequalityTransport := false
  suppliesCriticalScalingTransport := false

theorem navierAveragedEquationFullInterface_lab_positive_canary :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierAveragedEquationObligationsOnly_negative_canary :
    navierAveragedEquationObligationsOnlyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.missingChallengeWorldInterfaces =
        NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces ∧
      navierAveragedEquationObligationsOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierAveragedEquationInterfacesOnly_negative_canary :
    navierAveragedEquationInterfacesOnlyCanaryAudit.representedAllRequiredObligations =
        false ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.challengeWorldInterfacesClear =
        true ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.missingObligations =
        currentNavierAveragedEquationCompatibilityObligations ∧
      navierAveragedEquationInterfacesOnlyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierAveragedEquationObligationInterfacesWithoutWorldFamily_negative_canary :
    navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.representedAllRequiredObligations =
        true ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.challengeWorldInterfacesClear =
        false ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.missingChallengeWorldInterfaces =
        [ .averagedEquationWorldFamily ] ∧
      navierAveragedEquationObligationInterfacesWithoutWorldFamilyCanaryAudit.clearsAveragedEquationGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierAveragedMomentumOnly_negative_canary :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierCurrentEnergyBKMRouteAveragedEquationCanary_obstruction :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierAveragedEquationCanaries_guardrails :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NavierStokes
end FluidDynamics
end Mettapedia
