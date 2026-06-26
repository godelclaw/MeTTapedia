import Mettapedia.FluidDynamics.NavierStokes.Scaling.AveragedMomentumCanaries

/-!
# Navier-Stokes averaged-momentum canary regressions

Regression aliases for the finite averaged-momentum residual-balance canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem averaged_momentum_exact_residual_canary_regression :
    navierAveragedMomentumExactResidualCanaryAudit.residualVector =
        (1, -2, 3) ∧
      navierAveragedMomentumExactResidualCanaryAudit.representedBalanceVector =
        (1, -2, 3) ∧
      navierAveragedMomentumExactResidualCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumExactResidualCanaryAudit.clearsAveragedMomentumGate =
        true := by
  exact navierAveragedMomentumExactResidual_lab_positive_canary

theorem averaged_momentum_witness_mismatched_residual_canary_regression :
    navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact navierAveragedMomentumWitnessMismatchedResidual_negative_canary

theorem averaged_momentum_scalar_only_canary_regression :
    navierAveragedMomentumScalarOnlyCanaryAudit.scalarBalanceMatches =
        true ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact navierAveragedMomentumScalarOnly_negative_canary

theorem averaged_momentum_missing_world_family_canary_regression :
    navierAveragedMomentumMissingWorldFamilyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedEquationWorldFamily =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact navierAveragedMomentumMissingWorldFamily_negative_canary

theorem averaged_momentum_pointwise_only_canary_regression :
    navierAveragedMomentumPointwiseOnlyCanaryAudit.pointwiseMomentumEquationChecked =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.suppliesAveragedMomentumWitness =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact navierAveragedMomentumPointwiseOnly_negative_canary

theorem current_energy_bkm_route_averaged_momentum_canary_obstruction_regression :
    navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.suppliesFiniteEnergyL2Diagnostic =
        true ∧
      navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.suppliesAveragedEquationWorldFamily =
        false ∧
      navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.suppliesAveragedMomentumWitness =
        false ∧
      navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      NavierAveragedEquationObligation.averagedMomentumEquation.requiredWorldInterface =
        .averagedMomentumWitness := by
  exact navierCurrentEnergyBKMRouteAveragedMomentumCanary_obstruction

theorem averaged_momentum_canaries_guardrails_regression :
    navierAveragedMomentumExactResidualCanaryAudit.clearsAveragedMomentumGate =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.scalarBalanceMatches =
        true ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedEquationWorldFamily =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.clearsAveragedMomentumGate =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.pointwiseMomentumEquationChecked =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.suppliesAveragedMomentumWitness =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact navierAveragedMomentumCanaries_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
