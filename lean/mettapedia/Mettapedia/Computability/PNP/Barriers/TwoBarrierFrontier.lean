import Mettapedia.Computability.PNP.Barriers.OneBarrierFrontier

/-!
# PNP two-barrier frontier

This module records the checked negative boundary for replacement routes that
represent exactly two of the three classical PNP barrier layers.
-/

namespace Mettapedia.Computability.PNP

def currentPNPRelativizationNaturalProofRouteKey : String :=
  "pnp.relativization-natural-proof-replacement-candidate"

def currentPNPRelativizationNaturalProofBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPRelativizationNaturalProofRouteKey
  relativization := .cleared
  naturalProof := .cleared
  algebrization := .notRepresented

def currentPNPRelativizationNaturalProofWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPRelativizationNaturalProofRouteKey
  supplied :=
    [ .oracleChallengeWorldGenerator
    , .oracleInvariantSeparationClaim
    , .pseudorandomChallengeWorldSampler
    , .constructivityLargenessUsefulnessAudit
    , .nonNaturalEscapeCertificate
    ]

def currentPNPRelativizationNaturalProofEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPRelativizationNaturalProofRouteKey
  represented :=
    [ .nonrelativizingOracleSeparation
    , .nonNaturalPropertyEscape
    ]

def currentPNPRelativizationNaturalProofPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPRelativizationNaturalProofRouteKey
  status := currentPNPRelativizationNaturalProofBarrierStatus
  worldInterfaces := currentPNPRelativizationNaturalProofWorldInterfaces
  escapeLedger := currentPNPRelativizationNaturalProofEscapeLedger

theorem currentPNPRelativizationNaturalProofBarrierStatus_verdicts :
    currentPNPRelativizationNaturalProofBarrierStatus.relativization = .cleared ∧
      currentPNPRelativizationNaturalProofBarrierStatus.naturalProof = .cleared ∧
      currentPNPRelativizationNaturalProofBarrierStatus.algebrization =
        .notRepresented := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPRelativizationNaturalProof_missing_relativization :
    currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .relativization =
        [] := by
  simp [currentPNPRelativizationNaturalProofWorldInterfaces,
    currentPNPRelativizationNaturalProofEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationNaturalProof_missing_naturalProof :
    currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .naturalProof =
        [] := by
  simp [currentPNPRelativizationNaturalProofWorldInterfaces,
    currentPNPRelativizationNaturalProofEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationNaturalProof_missing_algebrization :
    currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses := by
  simp [currentPNPRelativizationNaturalProofWorldInterfaces,
    currentPNPRelativizationNaturalProofEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationNaturalProofBarrierStatus_not_cleared :
    ¬ currentPNPRelativizationNaturalProofBarrierStatus.ClearsAll := by
  intro hclears
  have halgebrization :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPRelativizationNaturalProofBarrierStatus hclears).2.2
  simp [currentPNPRelativizationNaturalProofBarrierStatus] at halgebrization

theorem currentPNPRelativizationNaturalProofPromotionGate_not_cleared :
    ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPRelativizationNaturalProofBarrierStatus_not_cleared hclears.1

theorem currentPNPRelativizationNaturalProofCandidate_clears_two_but_not_promotion :
    currentPNPRelativizationNaturalProofBarrierStatus.relativization = .cleared ∧
      currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .relativization =
        [] ∧
      currentPNPRelativizationNaturalProofBarrierStatus.naturalProof = .cleared ∧
      currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .naturalProof =
        [] ∧
      currentPNPRelativizationNaturalProofBarrierStatus.algebrization =
        .notRepresented ∧
      currentPNPRelativizationNaturalProofWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces ∧
      currentPNPRelativizationNaturalProofEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPRelativizationNaturalProofBarrierStatus_verdicts).1,
      (currentPNPRelativizationNaturalProof_missing_relativization).1,
      (currentPNPRelativizationNaturalProof_missing_relativization).2,
      (currentPNPRelativizationNaturalProofBarrierStatus_verdicts).2.1,
      (currentPNPRelativizationNaturalProof_missing_naturalProof).1,
      (currentPNPRelativizationNaturalProof_missing_naturalProof).2,
      (currentPNPRelativizationNaturalProofBarrierStatus_verdicts).2.2,
      (currentPNPRelativizationNaturalProof_missing_algebrization).1,
      (currentPNPRelativizationNaturalProof_missing_algebrization).2,
      currentPNPRelativizationNaturalProofPromotionGate_not_cleared⟩

def currentPNPRelativizationAlgebrizationRouteKey : String :=
  "pnp.relativization-algebrization-replacement-candidate"

def currentPNPRelativizationAlgebrizationBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPRelativizationAlgebrizationRouteKey
  relativization := .cleared
  naturalProof := .notRepresented
  algebrization := .cleared

def currentPNPRelativizationAlgebrizationWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPRelativizationAlgebrizationRouteKey
  supplied :=
    [ .oracleChallengeWorldGenerator
    , .oracleInvariantSeparationClaim
    , .algebraicOracleChallengeWorldGenerator
    , .algebraicLiftInterface
    , .algebraicOracleInvariantSeparationClaim
    ]

def currentPNPRelativizationAlgebrizationEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPRelativizationAlgebrizationRouteKey
  represented :=
    [ .nonrelativizingOracleSeparation
    , .nonAlgebrizingAlgebraicOracleSeparation
    ]

def currentPNPRelativizationAlgebrizationPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPRelativizationAlgebrizationRouteKey
  status := currentPNPRelativizationAlgebrizationBarrierStatus
  worldInterfaces := currentPNPRelativizationAlgebrizationWorldInterfaces
  escapeLedger := currentPNPRelativizationAlgebrizationEscapeLedger

theorem currentPNPRelativizationAlgebrizationBarrierStatus_verdicts :
    currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
        .cleared ∧
      currentPNPRelativizationAlgebrizationBarrierStatus.naturalProof =
        .notRepresented ∧
      currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
        .cleared := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPRelativizationAlgebrization_missing_relativization :
    currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .relativization =
        [] := by
  simp [currentPNPRelativizationAlgebrizationWorldInterfaces,
    currentPNPRelativizationAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationAlgebrization_missing_naturalProof :
    currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses := by
  simp [currentPNPRelativizationAlgebrizationWorldInterfaces,
    currentPNPRelativizationAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationAlgebrization_missing_algebrization :
    currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .algebrization =
        [] ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .algebrization =
        [] := by
  simp [currentPNPRelativizationAlgebrizationWorldInterfaces,
    currentPNPRelativizationAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPRelativizationAlgebrizationBarrierStatus_not_cleared :
    ¬ currentPNPRelativizationAlgebrizationBarrierStatus.ClearsAll := by
  intro hclears
  have hnaturalProof :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPRelativizationAlgebrizationBarrierStatus hclears).2.1
  simp [currentPNPRelativizationAlgebrizationBarrierStatus] at hnaturalProof

theorem currentPNPRelativizationAlgebrizationPromotionGate_not_cleared :
    ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPRelativizationAlgebrizationBarrierStatus_not_cleared hclears.1

theorem currentPNPRelativizationAlgebrizationCandidate_clears_two_but_not_promotion :
    currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
        .cleared ∧
      currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .relativization =
        [] ∧
      currentPNPRelativizationAlgebrizationBarrierStatus.naturalProof =
        .notRepresented ∧
      currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
        .cleared ∧
      currentPNPRelativizationAlgebrizationWorldInterfaces.missingFor .algebrization =
        [] ∧
      currentPNPRelativizationAlgebrizationEscapeLedger.missingFor .algebrization =
        [] ∧
      ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPRelativizationAlgebrizationBarrierStatus_verdicts).1,
      (currentPNPRelativizationAlgebrization_missing_relativization).1,
      (currentPNPRelativizationAlgebrization_missing_relativization).2,
      (currentPNPRelativizationAlgebrizationBarrierStatus_verdicts).2.1,
      (currentPNPRelativizationAlgebrization_missing_naturalProof).1,
      (currentPNPRelativizationAlgebrization_missing_naturalProof).2,
      (currentPNPRelativizationAlgebrizationBarrierStatus_verdicts).2.2,
      (currentPNPRelativizationAlgebrization_missing_algebrization).1,
      (currentPNPRelativizationAlgebrization_missing_algebrization).2,
      currentPNPRelativizationAlgebrizationPromotionGate_not_cleared⟩

def currentPNPNaturalProofAlgebrizationRouteKey : String :=
  "pnp.natural-proof-algebrization-replacement-candidate"

def currentPNPNaturalProofAlgebrizationBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPNaturalProofAlgebrizationRouteKey
  relativization := .notRepresented
  naturalProof := .cleared
  algebrization := .cleared

def currentPNPNaturalProofAlgebrizationWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPNaturalProofAlgebrizationRouteKey
  supplied :=
    [ .pseudorandomChallengeWorldSampler
    , .constructivityLargenessUsefulnessAudit
    , .nonNaturalEscapeCertificate
    , .algebraicOracleChallengeWorldGenerator
    , .algebraicLiftInterface
    , .algebraicOracleInvariantSeparationClaim
    ]

def currentPNPNaturalProofAlgebrizationEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPNaturalProofAlgebrizationRouteKey
  represented :=
    [ .nonNaturalPropertyEscape
    , .nonAlgebrizingAlgebraicOracleSeparation
    ]

def currentPNPNaturalProofAlgebrizationPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPNaturalProofAlgebrizationRouteKey
  status := currentPNPNaturalProofAlgebrizationBarrierStatus
  worldInterfaces := currentPNPNaturalProofAlgebrizationWorldInterfaces
  escapeLedger := currentPNPNaturalProofAlgebrizationEscapeLedger

theorem currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts :
    currentPNPNaturalProofAlgebrizationBarrierStatus.relativization =
        .notRepresented ∧
      currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
        .cleared ∧
      currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
        .cleared := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPNaturalProofAlgebrization_missing_relativization :
    currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses := by
  simp [currentPNPNaturalProofAlgebrizationWorldInterfaces,
    currentPNPNaturalProofAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofAlgebrization_missing_naturalProof :
    currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .naturalProof =
        [] := by
  simp [currentPNPNaturalProofAlgebrizationWorldInterfaces,
    currentPNPNaturalProofAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofAlgebrization_missing_algebrization :
    currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .algebrization =
        [] ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .algebrization =
        [] := by
  simp [currentPNPNaturalProofAlgebrizationWorldInterfaces,
    currentPNPNaturalProofAlgebrizationEscapeLedger,
    PNPBarrierRouteWorldInterfaces.missingFor,
    PNPBarrierEscapeLedger.missingFor,
    PNPBarrierKind.requiredWorldInterfaces,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPNaturalProofAlgebrizationBarrierStatus_not_cleared :
    ¬ currentPNPNaturalProofAlgebrizationBarrierStatus.ClearsAll := by
  intro hclears
  have hrelativization :=
    (PNPBarrierStatus.clearsAll_verdicts
      currentPNPNaturalProofAlgebrizationBarrierStatus hclears).1
  simp [currentPNPNaturalProofAlgebrizationBarrierStatus] at hrelativization

theorem currentPNPNaturalProofAlgebrizationPromotionGate_not_cleared :
    ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPNaturalProofAlgebrizationBarrierStatus_not_cleared hclears.1

theorem currentPNPNaturalProofAlgebrizationCandidate_clears_two_but_not_promotion :
    currentPNPNaturalProofAlgebrizationBarrierStatus.relativization =
        .notRepresented ∧
      currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
        .cleared ∧
      currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .naturalProof =
        [] ∧
      currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
        .cleared ∧
      currentPNPNaturalProofAlgebrizationWorldInterfaces.missingFor .algebrization =
        [] ∧
      currentPNPNaturalProofAlgebrizationEscapeLedger.missingFor .algebrization =
        [] ∧
      ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll := by
  exact
    ⟨(currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts).1,
      (currentPNPNaturalProofAlgebrization_missing_relativization).1,
      (currentPNPNaturalProofAlgebrization_missing_relativization).2,
      (currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts).2.1,
      (currentPNPNaturalProofAlgebrization_missing_naturalProof).1,
      (currentPNPNaturalProofAlgebrization_missing_naturalProof).2,
      (currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts).2.2,
      (currentPNPNaturalProofAlgebrization_missing_algebrization).1,
      (currentPNPNaturalProofAlgebrization_missing_algebrization).2,
      currentPNPNaturalProofAlgebrizationPromotionGate_not_cleared⟩

def currentPNPTwoBarrierCandidatePromotionGates :
    List PNPBarrierPromotionGate :=
  [ currentPNPRelativizationNaturalProofPromotionGate
  , currentPNPRelativizationAlgebrizationPromotionGate
  , currentPNPNaturalProofAlgebrizationPromotionGate
  ]

theorem currentPNPTwoBarrierCandidatePromotionGates_length :
    currentPNPTwoBarrierCandidatePromotionGates.length = 3 := by
  rfl

theorem currentPNPTwoBarrierCandidatePromotionGates_all_fail_promotion :
    ∀ gate ∈ currentPNPTwoBarrierCandidatePromotionGates,
      ¬ gate.ClearsAll := by
  intro gate hmem
  simp [currentPNPTwoBarrierCandidatePromotionGates] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact currentPNPRelativizationNaturalProofPromotionGate_not_cleared
  · exact currentPNPRelativizationAlgebrizationPromotionGate_not_cleared
  · exact currentPNPNaturalProofAlgebrizationPromotionGate_not_cleared

theorem currentPNPTwoBarrierCandidatePromotionGates_length_and_all_fail_promotion :
    currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPTwoBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact
    ⟨currentPNPTwoBarrierCandidatePromotionGates_length,
      currentPNPTwoBarrierCandidatePromotionGates_all_fail_promotion⟩

theorem currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion :
    (currentPNPRelativizationNaturalProofBarrierStatus.relativization =
        .cleared ∧
      currentPNPRelativizationNaturalProofBarrierStatus.naturalProof =
        .cleared ∧
      ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
          .cleared ∧
        currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll) := by
  exact
    ⟨⟨(currentPNPRelativizationNaturalProofBarrierStatus_verdicts).1,
        (currentPNPRelativizationNaturalProofBarrierStatus_verdicts).2.1,
        currentPNPRelativizationNaturalProofPromotionGate_not_cleared⟩,
      ⟨⟨(currentPNPRelativizationAlgebrizationBarrierStatus_verdicts).1,
          (currentPNPRelativizationAlgebrizationBarrierStatus_verdicts).2.2,
          currentPNPRelativizationAlgebrizationPromotionGate_not_cleared⟩,
        ⟨(currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts).2.1,
          (currentPNPNaturalProofAlgebrizationBarrierStatus_verdicts).2.2,
          currentPNPNaturalProofAlgebrizationPromotionGate_not_cleared⟩⟩⟩

end Mettapedia.Computability.PNP
