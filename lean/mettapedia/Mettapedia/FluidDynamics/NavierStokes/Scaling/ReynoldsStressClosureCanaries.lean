import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes Reynolds-stress closure canaries

Finite canaries for the residual-level Reynolds-stress closure gate in the
averaged-equation route.  The closure gate requires both a closure witness and
componentwise equality between the represented Reynolds-stress divergence and
the averaged momentum residual.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Finite audit input for a residual-level Reynolds-stress closure check. -/
structure NavierReynoldsStressClosureCanaryAudit where
  residualX : Int
  residualY : Int
  residualZ : Int
  stressDivergenceX : Int
  stressDivergenceY : Int
  stressDivergenceZ : Int
  suppliesReynoldsStressClosureWitness : Bool
  traceScalarMatches : Bool
  stressTensorSymmetric : Bool
  averagedVelocityZero : Bool
  pointwiseMomentumResidualZero : Bool
deriving DecidableEq, Repr

namespace NavierReynoldsStressClosureCanaryAudit

/-- Required averaged momentum residual as a finite three-component vector. -/
def residualVector
    (audit : NavierReynoldsStressClosureCanaryAudit) :
    Int × Int × Int :=
  (audit.residualX, audit.residualY, audit.residualZ)

/-- Represented divergence of the Reynolds stress as a finite three-component vector. -/
def stressDivergenceVector
    (audit : NavierReynoldsStressClosureCanaryAudit) :
    Int × Int × Int :=
  (audit.stressDivergenceX, audit.stressDivergenceY, audit.stressDivergenceZ)

/-- Whether the represented stress divergence closes the residual componentwise. -/
def residualMatches
    (audit : NavierReynoldsStressClosureCanaryAudit) : Bool :=
  (audit.stressDivergenceX == audit.residualX) &&
    (audit.stressDivergenceY == audit.residualY) &&
    (audit.stressDivergenceZ == audit.residualZ)

/-- Residual-level finite gate for Reynolds-stress closure. -/
def clearsClosureGate
    (audit : NavierReynoldsStressClosureCanaryAudit) : Bool :=
  audit.suppliesReynoldsStressClosureWitness &&
    audit.residualMatches

end NavierReynoldsStressClosureCanaryAudit

/-- Positive canary: a closure witness plus exact componentwise residual matching. -/
def navierReynoldsStressExactResidualCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 2
  residualY := -1
  residualZ := 3
  stressDivergenceX := 2
  stressDivergenceY := -1
  stressDivergenceZ := 3
  suppliesReynoldsStressClosureWitness := true
  traceScalarMatches := false
  stressTensorSymmetric := false
  averagedVelocityZero := false
  pointwiseMomentumResidualZero := false

/-- Negative canary: the witness label is present, but the residual does not match. -/
def navierReynoldsStressWitnessMismatchedResidualCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 2
  residualY := -1
  residualZ := 3
  stressDivergenceX := 2
  stressDivergenceY := 0
  stressDivergenceZ := 3
  suppliesReynoldsStressClosureWitness := true
  traceScalarMatches := false
  stressTensorSymmetric := false
  averagedVelocityZero := false
  pointwiseMomentumResidualZero := false

/-- Negative canary: a matching scalar trace does not replace vector residual closure. -/
def navierReynoldsStressTraceScalarOnlyCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 1
  residualY := 0
  residualZ := -1
  stressDivergenceX := 0
  stressDivergenceY := 0
  stressDivergenceZ := 0
  suppliesReynoldsStressClosureWitness := true
  traceScalarMatches := true
  stressTensorSymmetric := false
  averagedVelocityZero := false
  pointwiseMomentumResidualZero := false

/-- Negative canary: symmetry and matching residual data do not replace the witness. -/
def navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 0
  residualY := 4
  residualZ := -2
  stressDivergenceX := 0
  stressDivergenceY := 4
  stressDivergenceZ := -2
  suppliesReynoldsStressClosureWitness := false
  traceScalarMatches := false
  stressTensorSymmetric := true
  averagedVelocityZero := false
  pointwiseMomentumResidualZero := false

/-- Negative canary: zero-flow flags do not replace residual matching. -/
def navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 0
  residualY := 0
  residualZ := 0
  stressDivergenceX := 0
  stressDivergenceY := 1
  stressDivergenceZ := 0
  suppliesReynoldsStressClosureWitness := true
  traceScalarMatches := false
  stressTensorSymmetric := false
  averagedVelocityZero := true
  pointwiseMomentumResidualZero := true

/-- The current finite-energy/BKM route as a Reynolds-stress closure canary. -/
def navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit :
    NavierReynoldsStressClosureCanaryAudit where
  residualX := 0
  residualY := 0
  residualZ := 0
  stressDivergenceX := 0
  stressDivergenceY := 0
  stressDivergenceZ := 0
  suppliesReynoldsStressClosureWitness := false
  traceScalarMatches := false
  stressTensorSymmetric := false
  averagedVelocityZero := false
  pointwiseMomentumResidualZero := false

theorem navierReynoldsStressExactResidual_lab_positive_canary :
    navierReynoldsStressExactResidualCanaryAudit.residualVector =
        (2, -1, 3) ∧
      navierReynoldsStressExactResidualCanaryAudit.stressDivergenceVector =
        (2, -1, 3) ∧
      navierReynoldsStressExactResidualCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressExactResidualCanaryAudit.clearsClosureGate =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierReynoldsStressWitnessMismatchedResidual_negative_canary :
    navierReynoldsStressWitnessMismatchedResidualCanaryAudit.suppliesReynoldsStressClosureWitness =
        true ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressWitnessMismatchedResidualCanaryAudit.clearsClosureGate =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem navierReynoldsStressTraceScalarOnly_negative_canary :
    navierReynoldsStressTraceScalarOnlyCanaryAudit.traceScalarMatches =
        true ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressTraceScalarOnlyCanaryAudit.clearsClosureGate =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem navierReynoldsStressSymmetricStressWithoutWitness_negative_canary :
    navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.stressTensorSymmetric =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.residualMatches =
        true ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierReynoldsStressSymmetricStressWithoutWitnessCanaryAudit.clearsClosureGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierReynoldsStressZeroVelocityResidualMismatch_negative_canary :
    navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.averagedVelocityZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.pointwiseMomentumResidualZero =
        true ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.residualMatches =
        false ∧
      navierReynoldsStressZeroVelocityResidualMismatchCanaryAudit.clearsClosureGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierCurrentEnergyBKMRouteReynoldsStressClosureCanary_obstruction :
    navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.residualMatches =
        true ∧
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.suppliesReynoldsStressClosureWitness =
        false ∧
      navierCurrentEnergyBKMRouteReynoldsStressClosureCanaryAudit.clearsClosureGate =
        false ∧
      NavierAveragedEquationObligation.reynoldsStressClosure.requiredWorldInterface =
        .reynoldsStressClosureWitness := by
  exact
    ⟨rfl,
      rfl,
      rfl,
      rfl⟩

theorem navierReynoldsStressClosureCanaries_guardrails :
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
  exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NavierStokes
end FluidDynamics
end Mettapedia
