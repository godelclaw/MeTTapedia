import Mettapedia.Computability.PNP.Barriers.NaturalProofOnlyCandidate

/-!
# PNP algebrization-only candidate boundary

This module records a checked negative boundary for replacement routes: clearing
the algebrization layer alone is not enough to clear the global PNP promotion
gate.
-/

namespace Mettapedia.Computability.PNP

def currentPNPAlgebrizationOnlyRouteKey : String :=
  "pnp.algebrization-only-replacement-candidate"

def currentPNPAlgebrizationOnlyBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPAlgebrizationOnlyRouteKey
  relativization := .notRepresented
  naturalProof := .notRepresented
  algebrization := .cleared

def currentPNPAlgebrizationOnlyWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPAlgebrizationOnlyRouteKey
  supplied :=
    [ .algebraicOracleChallengeWorldGenerator
    , .algebraicLiftInterface
    , .algebraicOracleInvariantSeparationClaim
    ]

def currentPNPAlgebrizationOnlyEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPAlgebrizationOnlyRouteKey
  represented :=
    [ .nonAlgebrizingAlgebraicOracleSeparation
    ]

def currentPNPAlgebrizationOnlyPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPAlgebrizationOnlyRouteKey
  status := currentPNPAlgebrizationOnlyBarrierStatus
  worldInterfaces := currentPNPAlgebrizationOnlyWorldInterfaces
  escapeLedger := currentPNPAlgebrizationOnlyEscapeLedger

theorem currentPNPAlgebrizationOnlyBarrierStatus_verdicts :
    currentPNPAlgebrizationOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPAlgebrizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPAlgebrizationOnlyWorldInterfaces_missing_relativization :
    currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .relativization =
      PNPBarrierKind.relativization.requiredWorldInterfaces := by
  simp [currentPNPAlgebrizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPAlgebrizationOnlyWorldInterfaces_missing_naturalProof :
    currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredWorldInterfaces := by
  simp [currentPNPAlgebrizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPAlgebrizationOnlyWorldInterfaces_missing_algebrization :
    currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .algebrization =
      [] := by
  simp [currentPNPAlgebrizationOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPAlgebrizationOnlyEscapeLedger_missing_relativization :
    currentPNPAlgebrizationOnlyEscapeLedger.missingFor .relativization =
      PNPBarrierKind.relativization.requiredEscapeWitnesses := by
  simp [currentPNPAlgebrizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPAlgebrizationOnlyEscapeLedger_missing_naturalProof :
    currentPNPAlgebrizationOnlyEscapeLedger.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredEscapeWitnesses := by
  simp [currentPNPAlgebrizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPAlgebrizationOnlyEscapeLedger_missing_algebrization :
    currentPNPAlgebrizationOnlyEscapeLedger.missingFor .algebrization =
      [] := by
  simp [currentPNPAlgebrizationOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPAlgebrizationOnlyBarrierStatus_not_cleared :
    ¬ currentPNPAlgebrizationOnlyBarrierStatus.ClearsAll := by
  intro hclears
  have hrelativization :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPAlgebrizationOnlyBarrierStatus hclears).1
  simp [currentPNPAlgebrizationOnlyBarrierStatus] at hrelativization

theorem currentPNPAlgebrizationOnlyPromotionGate_not_cleared :
    ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPAlgebrizationOnlyBarrierStatus_not_cleared hclears.1

theorem currentPNPAlgebrizationOnlyCandidate_clears_algebrization_but_not_promotion :
    currentPNPAlgebrizationOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPAlgebrizationOnlyBarrierStatus.naturalProof = .notRepresented ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
      currentPNPAlgebrizationOnlyWorldInterfaces.missingFor .algebrization = [] ∧
      currentPNPAlgebrizationOnlyEscapeLedger.missingFor .algebrization = [] ∧
      ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPAlgebrizationOnlyBarrierStatus_verdicts).1,
      currentPNPAlgebrizationOnlyWorldInterfaces_missing_relativization,
      currentPNPAlgebrizationOnlyEscapeLedger_missing_relativization,
      (currentPNPAlgebrizationOnlyBarrierStatus_verdicts).2.1,
      currentPNPAlgebrizationOnlyWorldInterfaces_missing_naturalProof,
      currentPNPAlgebrizationOnlyEscapeLedger_missing_naturalProof,
      (currentPNPAlgebrizationOnlyBarrierStatus_verdicts).2.2,
      currentPNPAlgebrizationOnlyWorldInterfaces_missing_algebrization,
      currentPNPAlgebrizationOnlyEscapeLedger_missing_algebrization,
      currentPNPAlgebrizationOnlyPromotionGate_not_cleared⟩

end Mettapedia.Computability.PNP
