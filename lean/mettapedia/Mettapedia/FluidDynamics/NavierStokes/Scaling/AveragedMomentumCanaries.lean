import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes averaged-momentum canaries

Finite canaries for the averaged-momentum equation gate in the
averaged-equation route.  The gate requires componentwise residual balance
together with the averaged-equation world family and averaged-momentum witness
interfaces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Finite audit input for an averaged-momentum residual-balance check. -/
structure NavierAveragedMomentumCanaryAudit where
  residualX : Int
  residualY : Int
  residualZ : Int
  representedBalanceX : Int
  representedBalanceY : Int
  representedBalanceZ : Int
  suppliesAveragedEquationWorldFamily : Bool
  suppliesAveragedMomentumWitness : Bool
  scalarBalanceMatches : Bool
  pointwiseMomentumEquationChecked : Bool
  suppliesFiniteEnergyL2Diagnostic : Bool
deriving DecidableEq, Repr

namespace NavierAveragedMomentumCanaryAudit

/-- Averaged-momentum residual as a finite three-component vector. -/
def residualVector
    (audit : NavierAveragedMomentumCanaryAudit) : Int × Int × Int :=
  (audit.residualX, audit.residualY, audit.residualZ)

/-- Represented averaged-momentum balance as a finite three-component vector. -/
def representedBalanceVector
    (audit : NavierAveragedMomentumCanaryAudit) : Int × Int × Int :=
  (audit.representedBalanceX, audit.representedBalanceY,
    audit.representedBalanceZ)

/-- Whether the represented balance matches the residual componentwise. -/
def componentwiseResidualMatches
    (audit : NavierAveragedMomentumCanaryAudit) : Bool :=
  (audit.representedBalanceX == audit.residualX) &&
    (audit.representedBalanceY == audit.residualY) &&
    (audit.representedBalanceZ == audit.residualZ)

/-- Finite gate for averaged-momentum compatibility. -/
def clearsAveragedMomentumGate
    (audit : NavierAveragedMomentumCanaryAudit) : Bool :=
  audit.suppliesAveragedEquationWorldFamily &&
    audit.suppliesAveragedMomentumWitness &&
    audit.componentwiseResidualMatches

end NavierAveragedMomentumCanaryAudit

/-- Positive canary: componentwise balance with world family and witness. -/
def navierAveragedMomentumExactResidualCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 1
  residualY := -2
  residualZ := 3
  representedBalanceX := 1
  representedBalanceY := -2
  representedBalanceZ := 3
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  scalarBalanceMatches := false
  pointwiseMomentumEquationChecked := false
  suppliesFiniteEnergyL2Diagnostic := false

/-- Negative canary: a witness label cannot close a mismatched residual. -/
def navierAveragedMomentumWitnessMismatchedResidualCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 1
  residualY := -2
  residualZ := 3
  representedBalanceX := 1
  representedBalanceY := 0
  representedBalanceZ := 3
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  scalarBalanceMatches := false
  pointwiseMomentumEquationChecked := false
  suppliesFiniteEnergyL2Diagnostic := false

/-- Negative canary: scalar balance does not replace vector residual equality. -/
def navierAveragedMomentumScalarOnlyCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 2
  residualY := -1
  residualZ := 0
  representedBalanceX := 1
  representedBalanceY := 0
  representedBalanceZ := 0
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := true
  scalarBalanceMatches := true
  pointwiseMomentumEquationChecked := false
  suppliesFiniteEnergyL2Diagnostic := false

/-- Negative canary: residual balance still needs the averaged-equation world. -/
def navierAveragedMomentumMissingWorldFamilyCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 0
  residualY := 4
  residualZ := -2
  representedBalanceX := 0
  representedBalanceY := 4
  representedBalanceZ := -2
  suppliesAveragedEquationWorldFamily := false
  suppliesAveragedMomentumWitness := true
  scalarBalanceMatches := false
  pointwiseMomentumEquationChecked := false
  suppliesFiniteEnergyL2Diagnostic := false

/-- Negative canary: a pointwise flag does not supply the averaged witness. -/
def navierAveragedMomentumPointwiseOnlyCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 0
  residualY := 0
  residualZ := 0
  representedBalanceX := 0
  representedBalanceY := 0
  representedBalanceZ := 0
  suppliesAveragedEquationWorldFamily := true
  suppliesAveragedMomentumWitness := false
  scalarBalanceMatches := false
  pointwiseMomentumEquationChecked := true
  suppliesFiniteEnergyL2Diagnostic := false

/-- The current finite-energy/BKM route as an averaged-momentum canary. -/
def navierCurrentEnergyBKMRouteAveragedMomentumCanaryAudit :
    NavierAveragedMomentumCanaryAudit where
  residualX := 0
  residualY := 0
  residualZ := 0
  representedBalanceX := 0
  representedBalanceY := 0
  representedBalanceZ := 0
  suppliesAveragedEquationWorldFamily := false
  suppliesAveragedMomentumWitness := false
  scalarBalanceMatches := false
  pointwiseMomentumEquationChecked := false
  suppliesFiniteEnergyL2Diagnostic := true

theorem navierAveragedMomentumExactResidual_lab_positive_canary :
    navierAveragedMomentumExactResidualCanaryAudit.residualVector =
        (1, -2, 3) ∧
      navierAveragedMomentumExactResidualCanaryAudit.representedBalanceVector =
        (1, -2, 3) ∧
      navierAveragedMomentumExactResidualCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumExactResidualCanaryAudit.clearsAveragedMomentumGate =
        true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierAveragedMomentumWitnessMismatchedResidual_negative_canary :
    navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumWitnessMismatchedResidualCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem navierAveragedMomentumScalarOnly_negative_canary :
    navierAveragedMomentumScalarOnlyCanaryAudit.scalarBalanceMatches =
        true ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.componentwiseResidualMatches =
        false ∧
      navierAveragedMomentumScalarOnlyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact ⟨rfl, rfl, rfl⟩

theorem navierAveragedMomentumMissingWorldFamily_negative_canary :
    navierAveragedMomentumMissingWorldFamilyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedMomentumWitness =
        true ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.suppliesAveragedEquationWorldFamily =
        false ∧
      navierAveragedMomentumMissingWorldFamilyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierAveragedMomentumPointwiseOnly_negative_canary :
    navierAveragedMomentumPointwiseOnlyCanaryAudit.pointwiseMomentumEquationChecked =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.componentwiseResidualMatches =
        true ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.suppliesAveragedMomentumWitness =
        false ∧
      navierAveragedMomentumPointwiseOnlyCanaryAudit.clearsAveragedMomentumGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem navierCurrentEnergyBKMRouteAveragedMomentumCanary_obstruction :
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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem navierAveragedMomentumCanaries_guardrails :
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
  exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NavierStokes
end FluidDynamics
end Mettapedia
