import Mettapedia.Computability.PNP.Barriers.RelativizationOnlyCandidate

/-!
# PNP natural-proof-only candidate boundary

This module records a checked negative boundary for replacement routes: clearing
the natural-proofs layer alone is not enough to clear the global PNP promotion
gate.
-/

namespace Mettapedia.Computability.PNP

def currentPNPNaturalProofOnlyRouteKey : String :=
  "pnp.natural-proof-only-replacement-candidate"

def currentPNPNaturalProofOnlyBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPNaturalProofOnlyRouteKey
  relativization := .notRepresented
  naturalProof := .cleared
  algebrization := .notRepresented

def currentPNPNaturalProofOnlyWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPNaturalProofOnlyRouteKey
  supplied :=
    [ .pseudorandomChallengeWorldSampler
    , .constructivityLargenessUsefulnessAudit
    , .nonNaturalEscapeCertificate
    ]

def currentPNPNaturalProofOnlyEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPNaturalProofOnlyRouteKey
  represented :=
    [ .nonNaturalPropertyEscape
    ]

def currentPNPNaturalProofOnlyPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPNaturalProofOnlyRouteKey
  status := currentPNPNaturalProofOnlyBarrierStatus
  worldInterfaces := currentPNPNaturalProofOnlyWorldInterfaces
  escapeLedger := currentPNPNaturalProofOnlyEscapeLedger

theorem currentPNPNaturalProofOnlyBarrierStatus_verdicts :
    currentPNPNaturalProofOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
      currentPNPNaturalProofOnlyBarrierStatus.algebrization = .notRepresented := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPNaturalProofOnlyWorldInterfaces_missing_relativization :
    currentPNPNaturalProofOnlyWorldInterfaces.missingFor .relativization =
      PNPBarrierKind.relativization.requiredWorldInterfaces := by
  simp [currentPNPNaturalProofOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPNaturalProofOnlyWorldInterfaces_missing_naturalProof :
    currentPNPNaturalProofOnlyWorldInterfaces.missingFor .naturalProof =
      [] := by
  simp [currentPNPNaturalProofOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPNaturalProofOnlyWorldInterfaces_missing_algebrization :
    currentPNPNaturalProofOnlyWorldInterfaces.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  simp [currentPNPNaturalProofOnlyWorldInterfaces,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPNaturalProofOnlyEscapeLedger_missing_relativization :
    currentPNPNaturalProofOnlyEscapeLedger.missingFor .relativization =
      PNPBarrierKind.relativization.requiredEscapeWitnesses := by
  simp [currentPNPNaturalProofOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofOnlyEscapeLedger_missing_naturalProof :
    currentPNPNaturalProofOnlyEscapeLedger.missingFor .naturalProof =
      [] := by
  simp [currentPNPNaturalProofOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofOnlyEscapeLedger_missing_algebrization :
    currentPNPNaturalProofOnlyEscapeLedger.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredEscapeWitnesses := by
  simp [currentPNPNaturalProofOnlyEscapeLedger,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofOnlyBarrierStatus_not_cleared :
    ¬ currentPNPNaturalProofOnlyBarrierStatus.ClearsAll := by
  intro hclears
  have hrelativization :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPNaturalProofOnlyBarrierStatus hclears).1
  simp [currentPNPNaturalProofOnlyBarrierStatus] at hrelativization

theorem currentPNPNaturalProofOnlyPromotionGate_not_cleared :
    ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPNaturalProofOnlyBarrierStatus_not_cleared hclears.1

theorem currentPNPNaturalProofOnlyCandidate_clears_naturalProof_but_not_promotion :
    currentPNPNaturalProofOnlyBarrierStatus.relativization = .notRepresented ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .naturalProof = [] ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .naturalProof = [] ∧
      currentPNPNaturalProofOnlyBarrierStatus.algebrization = .notRepresented ∧
      currentPNPNaturalProofOnlyWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPNaturalProofOnlyEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPNaturalProofOnlyBarrierStatus_verdicts).1,
      currentPNPNaturalProofOnlyWorldInterfaces_missing_relativization,
      currentPNPNaturalProofOnlyEscapeLedger_missing_relativization,
      (currentPNPNaturalProofOnlyBarrierStatus_verdicts).2.1,
      currentPNPNaturalProofOnlyWorldInterfaces_missing_naturalProof,
      currentPNPNaturalProofOnlyEscapeLedger_missing_naturalProof,
      (currentPNPNaturalProofOnlyBarrierStatus_verdicts).2.2,
      currentPNPNaturalProofOnlyWorldInterfaces_missing_algebrization,
      currentPNPNaturalProofOnlyEscapeLedger_missing_algebrization,
      currentPNPNaturalProofOnlyPromotionGate_not_cleared⟩

end Mettapedia.Computability.PNP
