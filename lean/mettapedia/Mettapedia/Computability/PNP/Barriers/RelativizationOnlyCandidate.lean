import Mettapedia.Computability.PNP.Barriers.ReplacementGate

/-!
# PNP relativization-only candidate boundary

This module records a checked negative boundary for replacement routes: clearing
the relativization layer alone is not enough to clear the global PNP promotion
gate.
-/

namespace Mettapedia.Computability.PNP

def currentPNPRelativizationOnlyRouteKey : String :=
  "pnp.relativization-only-replacement-candidate"

def currentPNPRelativizationOnlyBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPRelativizationOnlyRouteKey
  relativization := .cleared
  naturalProof := .notRepresented
  algebrization := .notRepresented

def currentPNPRelativizationOnlyWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPRelativizationOnlyRouteKey
  supplied :=
    [ .oracleChallengeWorldGenerator
    , .oracleInvariantSeparationClaim
    ]

def currentPNPRelativizationOnlyEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPRelativizationOnlyRouteKey
  represented :=
    [ .nonrelativizingOracleSeparation
    ]

def currentPNPRelativizationOnlyPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPRelativizationOnlyRouteKey
  status := currentPNPRelativizationOnlyBarrierStatus
  worldInterfaces := currentPNPRelativizationOnlyWorldInterfaces
  escapeLedger := currentPNPRelativizationOnlyEscapeLedger

theorem currentPNPRelativizationOnlyBarrierStatus_verdicts :
    currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
      currentPNPRelativizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPRelativizationOnlyBarrierStatus.algebrization = .notRepresented := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPRelativizationOnlyWorldInterfaces_missing_relativization :
    currentPNPRelativizationOnlyWorldInterfaces.missingFor .relativization =
      [] := by
  simp [currentPNPRelativizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPRelativizationOnlyWorldInterfaces_missing_naturalProof :
    currentPNPRelativizationOnlyWorldInterfaces.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredWorldInterfaces := by
  simp [currentPNPRelativizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPRelativizationOnlyWorldInterfaces_missing_algebrization :
    currentPNPRelativizationOnlyWorldInterfaces.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  simp [currentPNPRelativizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPRelativizationOnlyEscapeLedger_missing_relativization :
    currentPNPRelativizationOnlyEscapeLedger.missingFor .relativization =
      [] := by
  simp [currentPNPRelativizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationOnlyEscapeLedger_missing_naturalProof :
    currentPNPRelativizationOnlyEscapeLedger.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredEscapeWitnesses := by
  simp [currentPNPRelativizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationOnlyEscapeLedger_missing_algebrization :
    currentPNPRelativizationOnlyEscapeLedger.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredEscapeWitnesses := by
  simp [currentPNPRelativizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationOnlyBarrierStatus_not_cleared :
    ¬ currentPNPRelativizationOnlyBarrierStatus.ClearsAll := by
  intro hclears
  have hnatural :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPRelativizationOnlyBarrierStatus hclears).2.1
  simp [currentPNPRelativizationOnlyBarrierStatus] at hnatural

theorem currentPNPRelativizationOnlyPromotionGate_not_cleared :
    ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPRelativizationOnlyBarrierStatus_not_cleared hclears.1

theorem currentPNPRelativizationOnlyCandidate_clears_relativization_but_not_promotion :
    currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .relativization = [] ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .relativization = [] ∧
      currentPNPRelativizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPRelativizationOnlyBarrierStatus.algebrization = .notRepresented ∧
      currentPNPRelativizationOnlyWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPRelativizationOnlyEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPRelativizationOnlyBarrierStatus_verdicts).1,
      currentPNPRelativizationOnlyWorldInterfaces_missing_relativization,
      currentPNPRelativizationOnlyEscapeLedger_missing_relativization,
      (currentPNPRelativizationOnlyBarrierStatus_verdicts).2.1,
      currentPNPRelativizationOnlyWorldInterfaces_missing_naturalProof,
      currentPNPRelativizationOnlyEscapeLedger_missing_naturalProof,
      (currentPNPRelativizationOnlyBarrierStatus_verdicts).2.2,
      currentPNPRelativizationOnlyWorldInterfaces_missing_algebrization,
      currentPNPRelativizationOnlyEscapeLedger_missing_algebrization,
      currentPNPRelativizationOnlyPromotionGate_not_cleared⟩

end Mettapedia.Computability.PNP
