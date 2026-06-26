import Mettapedia.FluidDynamics.NavierStokes.Scaling.CriticalNormCanaries

/-!
# Navier-Stokes critical-norm canary regressions

Regression aliases for the finite critical-norm canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem critical_l3_full_interface_canary_regression :
    navierCriticalL3FullInterfaceCanaryAudit.regime = .critical ∧
      navierCriticalL3FullInterfaceCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3FullInterfaceCanaryAudit.missingCriticalWorldInterfaces =
        [] ∧
      navierCriticalL3FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true := by
  exact navierCriticalL3FullInterface_lab_positive_canary

theorem subcritical_l4_full_interface_canary_regression :
    navierSubcriticalL4FullInterfaceCanaryAudit.regime = .subcritical ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.missingCriticalWorldInterfaces =
        [] ∧
      navierSubcriticalL4FullInterfaceCanaryAudit.clearsCriticalNormGate =
        true := by
  exact navierSubcriticalL4FullInterface_lab_positive_canary

theorem finite_energy_l2_only_canary_regression :
    navierFiniteEnergyL2OnlyCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierFiniteEnergyL2OnlyCanaryAudit.regime = .supercritical ∧
      navierFiniteEnergyL2OnlyCanaryAudit.diagnosticClearsCriticalPromotion =
        false ∧
      navierFiniteEnergyL2OnlyCanaryAudit.missingCriticalWorldInterfaces =
        NavierScalingCheck.criticalNorm.requiredWorldInterfaces ∧
      navierFiniteEnergyL2OnlyCanaryAudit.clearsCriticalNormGate =
        false := by
  exact navierFiniteEnergyL2Only_negative_canary

theorem critical_l3_missing_witness_canary_regression :
    navierCriticalL3MissingWitnessCanaryAudit.regime = .critical ∧
      navierCriticalL3MissingWitnessCanaryAudit.diagnosticClearsCriticalPromotion =
        true ∧
      navierCriticalL3MissingWitnessCanaryAudit.missingCriticalWorldInterfaces =
        [ .criticalNormControlWitness ] ∧
      navierCriticalL3MissingWitnessCanaryAudit.clearsCriticalNormGate =
        false := by
  exact navierCriticalL3MissingWitness_negative_canary

theorem supercritical_l2_with_interfaces_canary_regression :
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
  exact navierSupercriticalL2WithInterfaces_negative_canary

theorem current_energy_bkm_route_critical_norm_canary_obstruction_regression :
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
  exact navierCurrentEnergyBKMRouteCriticalNormCanary_obstruction

theorem critical_norm_canaries_guardrails_regression :
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
  exact navierCriticalNormCanaries_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
