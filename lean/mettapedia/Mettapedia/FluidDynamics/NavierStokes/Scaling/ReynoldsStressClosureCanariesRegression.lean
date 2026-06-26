import Mettapedia.FluidDynamics.NavierStokes.Scaling.ReynoldsStressClosureCanaries

/-!
# Navier-Stokes Reynolds-stress closure canary regressions

Regression aliases for the finite Reynolds-stress residual-closure canaries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Scaling
namespace Regression

theorem reynolds_stress_exact_residual_canary_regression :
    navierReynoldsStressExactResidualCanaryAudit.residualVector =
        (2, -1, 3) ∧
      navierReynoldsStressExactResidualCanaryAudit.stressDivergenceVector =
        (2, -1, 3) ∧
      navierReynoldsStressExactResidualCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressExactResidualCanaryAudit.clearsClosureGate =
        true := by
  exact navierReynoldsStressExactResidual_lab_positive_canary

theorem reynolds_stress_witness_mismatched_residual_canary_regression :
    navierReynoldsStressWitnessMismatchedResidualCanaryAudit.suppliesReynoldsStressClosureWitness =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.clearsClosureGate =
        false := by
  exact navierReynoldsStressWitnessMismatchedResidual_negative_canary

theorem reynolds_stress_trace_scalar_only_canary_regression :
    navierReynoldsStressTraceScalarOnlyCanaryAudit.traceScalarMatches =
        true ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.clearsClosureGate =
        false := by
  exact navierReynoldsStressTraceScalarOnly_negative_canary

theorem reynolds_stress_symmetric_stress_without_witness_canary_regression :
    navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.stressTensorSymmetric =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.clearsClosureGate =
        false := by
  exact navierReynoldsStressSymmetricStressWithoutWitness_negative_canary

theorem reynolds_stress_zero_velocity_residual_mismatch_canary_regression :
    navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.averagedVelocityZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.pointwiseMomentumResidualZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.clearsClosureGate =
        false := by
  exact navierReynoldsStressZeroVelocityResidualMismatch_negative_canary

theorem current_energy_bkm_route_reynolds_stress_closure_canary_obstruction_regression :
    navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.residualMatches =
        true ∧
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.clearsClosureGate =
        false ∧
      NavierAveragedEquationObligation.reynoldsStressClosure.requiredWorldInterface =
        .reynoldsStressClosureWitness := by
  exact navierCurrentEnergyBKMRouteReynoldsStressClosureCanary_obstruction

theorem reynolds_stress_closure_canaries_guardrails_regression :
    navierReynoldsStressExactResidualCanaryAudit.clearsClosureGate =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.suppliesReynoldsStressClosureWitness =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.traceScalarMatches =
        true ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.clearsClosureGate =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.averagedVelocityZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.pointwiseMomentumResidualZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.clearsClosureGate =
        false := by
  exact navierReynoldsStressClosureCanaries_guardrails

end Regression
end Scaling
end NavierStokes
end FluidDynamics
end Mettapedia
