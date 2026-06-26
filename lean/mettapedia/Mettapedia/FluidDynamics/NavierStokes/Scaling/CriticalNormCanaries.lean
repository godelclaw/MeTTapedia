import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes critical-norm canaries

Finite canaries for the critical-norm gate in the Navier-Stokes scaling layer.
The current finite-energy/BKM route records an `L^2` diagnostic; these canaries
keep separate the diagnostic scale requirement and the critical-world interface
requirements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Finite audit input for the Navier-Stokes critical-norm promotion gate. -/
structure NavierCriticalNormCanaryAudit where
  velocityLpIndex : Nat
  suppliesFiniteEnergyL2Diagnostic : Bool
  suppliesCriticalInitialDataFamily : Bool
  suppliesCriticalNormControlWitness : Bool
deriving DecidableEq, Repr

namespace NavierCriticalNormCanaryAudit

/-- Coarse scaling regime of the audit's velocity diagnostic. -/
def regime (audit : NavierCriticalNormCanaryAudit) : NavierScalingRegime :=
  velocityLpScalingRegime audit.velocityLpIndex

/-- Whether the audit's velocity diagnostic is critical or better. -/
def diagnosticClearsCriticalPromotion
    (audit : NavierCriticalNormCanaryAudit) : Bool :=
  velocityLpClearsCriticalPromotion audit.velocityLpIndex

/-- Whether both critical-world interfaces for the critical-norm check are present. -/
def criticalWorldInterfacesClear
    (audit : NavierCriticalNormCanaryAudit) : Bool :=
  audit.suppliesCriticalInitialDataFamily &&
    audit.suppliesCriticalNormControlWitness

/-- Missing critical-world interfaces for the critical-norm check. -/
def missingCriticalWorldInterfaces
    (audit : NavierCriticalNormCanaryAudit) :
    List NavierScalingWorldInterface :=
  (if audit.suppliesCriticalInitialDataFamily then
      []
    else
      [ .criticalInitialDataFamily ]) ++
    if audit.suppliesCriticalNormControlWitness then
      []
    else
      [ .criticalNormControlWitness ]

/-- Critical-norm gate for the finite canaries. -/
def clearsCriticalNormGate
    (audit : NavierCriticalNormCanaryAudit) : Bool :=
  audit.diagnosticClearsCriticalPromotion &&
    audit.criticalWorldInterfacesClear

end NavierCriticalNormCanaryAudit

/-- Positive canary: critical `L^3` diagnostic with both critical-world interfaces. -/
def navierCriticalL3FullInterfaceCanaryAudit :
    NavierCriticalNormCanaryAudit where
  velocityLpIndex := 3
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesCriticalInitialDataFamily := true
  suppliesCriticalNormControlWitness := true

/-- Positive canary: subcritical `L^4` diagnostic with both critical-world interfaces. -/
def navierSubcriticalL4FullInterfaceCanaryAudit :
    NavierCriticalNormCanaryAudit where
  velocityLpIndex := 4
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesCriticalInitialDataFamily := true
  suppliesCriticalNormControlWitness := true

/-- Negative canary: finite-energy `L^2` diagnostic alone. -/
def navierFiniteEnergyL2OnlyCanaryAudit :
    NavierCriticalNormCanaryAudit where
  velocityLpIndex := finiteEnergyVelocityLpIndex
  suppliesFiniteEnergyL2Diagnostic := true
  suppliesCriticalInitialDataFamily := false
  suppliesCriticalNormControlWitness := false

/-- Negative canary: critical `L^3` diagnostic without the norm-control witness. -/
def navierCriticalL3MissingWitnessCanaryAudit :
    NavierCriticalNormCanaryAudit where
  velocityLpIndex := criticalVelocityLpIndex
  suppliesFiniteEnergyL2Diagnostic := false
  suppliesCriticalInitialDataFamily := true
  suppliesCriticalNormControlWitness := false

/-- Negative canary: critical-world interfaces do not repair a supercritical diagnostic. -/
def navierSupercriticalL2WithInterfacesCanaryAudit :
    NavierCriticalNormCanaryAudit where
  velocityLpIndex := finiteEnergyVelocityLpIndex
  suppliesFiniteEnergyL2Diagnostic := true
  suppliesCriticalInitialDataFamily := true
  suppliesCriticalNormControlWitness := true

/-- The current finite-energy/BKM route's critical-norm canary audit. -/
def navierCurrentEnergyBKMRouteCriticalNormCanaryAudit :
    NavierCriticalNormCanaryAudit :=
  navierFiniteEnergyL2OnlyCanaryAudit

theorem navierCriticalL3FullInterface_lab_positive_canary :
    navierCriticalL3FullInterfaceCanaryAudit.regime = .critical ∧
      navierCriticalL3FullInterfaceCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3FullInterfaceCanaryAudit.missingCriticalWorldInterfaces =
        [] ∧
      navierCriticalL3FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierSubcriticalL4FullInterface_lab_positive_canary :
    navierSubcriticalL4FullInterfaceCanaryAudit.regime = .subcritical ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.missingCriticalWorldInterfaces =
        [] ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierFiniteEnergyL2Only_negative_canary :
    navierFiniteEnergyL2OnlyCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierFiniteEnergyL2OnlyCanaryAudit.regime = .supercritical ∧
      navierFiniteEnergyL2OnlyCanaryAudit.diagnosticClearsCriticalPromotion =
        false ∧
      navierFiniteEnergyL2OnlyCanaryAudit.missingCriticalWorldInterfaces =
        NavierScalingCheck.criticalNorm.requiredWorldInterfaces ∧
      navierFiniteEnergyL2OnlyCanaryAudit.clearsCriticalNormGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierCriticalL3MissingWitness_negative_canary :
    navierCriticalL3MissingWitnessCanaryAudit.regime = .critical ∧
      navierCriticalL3MissingWitnessCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3MissingWitnessCanaryAudit.missingCriticalWorldInterfaces =
        [ .criticalNormControlWitness ] ∧
      navierCriticalL3MissingWitnessCanaryAudit.clearsCriticalNormGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierSupercriticalL2WithInterfaces_negative_canary :
    navierSupercriticalL2WithInterfacesCanaryAudit.regime =
        .supercritical ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.diagnosticClearsCriticalPromotion =
        false ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.criticalWorldInterfacesClear =
        true ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.missingCriticalWorldInterfaces =
        [] ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.clearsCriticalNormGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierCurrentEnergyBKMRouteCriticalNormCanary_obstruction :
    navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.velocityLpIndex =
        finiteEnergyVelocityLpIndex ∧
      navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.regime =
        .supercritical ∧
      navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.missingCriticalWorldInterfaces =
        NavierScalingCheck.criticalNorm.requiredWorldInterfaces ∧
      navierCurrentEnergyBKMRouteCriticalNormCanaryAudit.clearsCriticalNormGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem navierCriticalNormCanaries_guardrails :
    navierCriticalL3FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true ∧
      navierFiniteEnergyL2OnlyCanaryAudit.clearsCriticalNormGate =
        false ∧
      navierCriticalL3MissingWitnessCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3MissingWitnessCanaryAudit.clearsCriticalNormGate =
        false ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.criticalWorldInterfacesClear =
        true ∧
      navierSupercriticalL2WithInterfacesCanaryAudit.clearsCriticalNormGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NavierStokes
end FluidDynamics
end Mettapedia
