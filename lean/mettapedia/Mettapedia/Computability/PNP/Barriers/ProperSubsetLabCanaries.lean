import Mettapedia.Computability.PNP.Barriers.ProperSubsetFrontier

/-!
# PNP barrier-subset lab canaries

Finite canaries for the PNP barrier-promotion gate.  The full three-barrier
toy route clears the finite gate, while every proper subset of the
relativization, natural-proof, and algebrization layers fails promotion.
-/

namespace Mettapedia.Computability.PNP

/-- Finite Boolean audit input for the PNP barrier-subset frontier. -/
structure PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict : Bool
  naturalProofVerdict : Bool
  algebrizationVerdict : Bool
  relativizationWorldInterfaces : Bool
  naturalProofWorldInterfaces : Bool
  algebrizationWorldInterfaces : Bool
  relativizationEscapeWitness : Bool
  naturalProofEscapeWitness : Bool
  algebrizationEscapeWitness : Bool
deriving DecidableEq, Repr

namespace PNPBarrierSubsetFrontierCanaryAudit

/-- Whether all three barrier verdicts are represented as cleared. -/
def verdictLayerClears
    (audit : PNPBarrierSubsetFrontierCanaryAudit) : Bool :=
  audit.relativizationVerdict &&
    audit.naturalProofVerdict &&
    audit.algebrizationVerdict

/-- Whether all three challenge-world interface layers are supplied. -/
def worldInterfaceLayerClears
    (audit : PNPBarrierSubsetFrontierCanaryAudit) : Bool :=
  audit.relativizationWorldInterfaces &&
    audit.naturalProofWorldInterfaces &&
    audit.algebrizationWorldInterfaces

/-- Whether all three positive escape-witness layers are represented. -/
def escapeWitnessLayerClears
    (audit : PNPBarrierSubsetFrontierCanaryAudit) : Bool :=
  audit.relativizationEscapeWitness &&
    audit.naturalProofEscapeWitness &&
    audit.algebrizationEscapeWitness

/-- Finite Boolean promotion gate for the barrier-subset canaries. -/
def clearsGlobalPromotionGate
    (audit : PNPBarrierSubsetFrontierCanaryAudit) : Bool :=
  audit.verdictLayerClears &&
    audit.worldInterfaceLayerClears &&
    audit.escapeWitnessLayerClears

end PNPBarrierSubsetFrontierCanaryAudit

/-- Positive canary: all three barrier layers are represented. -/
def pnpBarrierSubsetAllThreeCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := true
  algebrizationVerdict := true
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := true

/-- Negative canary: the current local ledger supplies no barrier layers. -/
def pnpBarrierSubsetCurrentLocalLedgerCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := false
  algebrizationVerdict := false
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := false

/-- Negative canary: relativization alone is only a proper subset. -/
def pnpBarrierSubsetRelativizationOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := false
  algebrizationVerdict := false
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := false

/-- Negative canary: natural-proof escape alone is only a proper subset. -/
def pnpBarrierSubsetNaturalProofOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := true
  algebrizationVerdict := false
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := false

/-- Negative canary: algebrization alone is only a proper subset. -/
def pnpBarrierSubsetAlgebrizationOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := false
  algebrizationVerdict := true
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := true

/-- Negative canary: relativization plus natural-proof escape still omits algebrization. -/
def pnpBarrierSubsetRelativizationNaturalProofCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := true
  algebrizationVerdict := false
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := false

/-- Negative canary: relativization plus algebrization still omits natural proofs. -/
def pnpBarrierSubsetRelativizationAlgebrizationCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := false
  algebrizationVerdict := true
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := true

/-- Negative canary: natural-proof escape plus algebrization still omits relativization. -/
def pnpBarrierSubsetNaturalProofAlgebrizationCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := true
  algebrizationVerdict := true
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := true

/-- Negative canary: verdicts alone do not supply worlds or witnesses. -/
def pnpBarrierPromotionVerdictsOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := true
  algebrizationVerdict := true
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := false

/-- Negative canary: challenge-world interfaces alone do not supply verdicts or witnesses. -/
def pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := false
  algebrizationVerdict := false
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := false

/-- Negative canary: escape witnesses alone do not supply verdicts or worlds. -/
def pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := false
  algebrizationVerdict := false
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := true

/-- Negative canary: verdicts plus worlds still need positive escape witnesses. -/
def pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := true
  algebrizationVerdict := true
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := false
  naturalProofEscapeWitness := false
  algebrizationEscapeWitness := false

/-- Negative canary: verdicts plus witnesses still need challenge-world interfaces. -/
def pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := true
  naturalProofVerdict := true
  algebrizationVerdict := true
  relativizationWorldInterfaces := false
  naturalProofWorldInterfaces := false
  algebrizationWorldInterfaces := false
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := true

/-- Negative canary: worlds plus witnesses still need cleared verdicts. -/
def pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit :
    PNPBarrierSubsetFrontierCanaryAudit where
  relativizationVerdict := false
  naturalProofVerdict := false
  algebrizationVerdict := false
  relativizationWorldInterfaces := true
  naturalProofWorldInterfaces := true
  algebrizationWorldInterfaces := true
  relativizationEscapeWitness := true
  naturalProofEscapeWitness := true
  algebrizationEscapeWitness := true

theorem pnpBarrierSubsetAllThree_lab_positive_canary :
    pnpBarrierSubsetAllThreeCanaryAudit.verdictLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.worldInterfaceLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.escapeWitnessLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.clearsGlobalPromotionGate = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pnpBarrierSubsetCurrentLocalLedger_negative_canary :
    pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.verdictLayerClears = false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.worldInterfaceLayerClears =
        false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.escapeWitnessLayerClears =
        false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pnpBarrierSubsetProperSubsets_negative_canary :
    pnpBarrierSubsetRelativizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetAlgebrizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationNaturalProofCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pnpBarrierPromotionLayerOnly_negative_canary :
    pnpBarrierPromotionVerdictsOnlyCanaryAudit.verdictLayerClears = true ∧
      pnpBarrierPromotionVerdictsOnlyCanaryAudit.worldInterfaceLayerClears =
        false ∧
      pnpBarrierPromotionVerdictsOnlyCanaryAudit.escapeWitnessLayerClears =
        false ∧
      pnpBarrierPromotionVerdictsOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.verdictLayerClears =
        false ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.worldInterfaceLayerClears =
        true ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.escapeWitnessLayerClears =
        false ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.verdictLayerClears =
        false ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.worldInterfaceLayerClears =
        false ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.escapeWitnessLayerClears =
        true ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pnpBarrierPromotionLayerPairs_negative_canary :
    pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.verdictLayerClears =
        true ∧
      pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.worldInterfaceLayerClears =
        true ∧
      pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.escapeWitnessLayerClears =
        false ∧
      pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.verdictLayerClears =
        true ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.worldInterfaceLayerClears =
        false ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.escapeWitnessLayerClears =
        true ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.verdictLayerClears =
        false ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.worldInterfaceLayerClears =
        true ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.escapeWitnessLayerClears =
        true ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pnpBarrierPromotionLayerOmissions_guardrails :
    pnpBarrierPromotionVerdictsOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldInterfacesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionEscapeWitnessesOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionVerdictsWorldsNoEscapesCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionVerdictsEscapesNoWorldsCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierPromotionWorldsEscapesNoVerdictsCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pnpBarrierSubsetFrontierCanaries_guardrails :
    pnpBarrierSubsetAllThreeCanaryAudit.clearsGlobalPromotionGate = true ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetAlgebrizationOnlyCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationNaturalProofCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetRelativizationAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false ∧
      pnpBarrierSubsetNaturalProofAlgebrizationCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Toy route key for a finite route that represents all three barrier layers. -/
def currentPNPAllBarrierCandidateRouteKey : String :=
  "pnp.all-barrier-replacement-candidate"

/-- Positive finite canary: all three barrier verdicts are represented. -/
def currentPNPAllBarrierCandidateBarrierStatus : PNPBarrierStatus where
  routeKey := currentPNPAllBarrierCandidateRouteKey
  relativization := .cleared
  naturalProof := .cleared
  algebrization := .cleared

/-- Positive finite canary: all challenge-world interfaces are supplied. -/
def currentPNPAllBarrierCandidateWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := currentPNPAllBarrierCandidateRouteKey
  supplied :=
    [ .oracleChallengeWorldGenerator
    , .oracleInvariantSeparationClaim
    , .pseudorandomChallengeWorldSampler
    , .constructivityLargenessUsefulnessAudit
    , .nonNaturalEscapeCertificate
    , .algebraicOracleChallengeWorldGenerator
    , .algebraicLiftInterface
    , .algebraicOracleInvariantSeparationClaim
    ]

/-- Positive finite canary: all positive escape witnesses are represented. -/
def currentPNPAllBarrierCandidateEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := currentPNPAllBarrierCandidateRouteKey
  represented :=
    [ .nonrelativizingOracleSeparation
    , .nonNaturalPropertyEscape
    , .nonAlgebrizingAlgebraicOracleSeparation
    ]

/-- Positive finite canary: all three promotion layers are represented. -/
def currentPNPAllBarrierCandidatePromotionGate :
    PNPBarrierPromotionGate where
  routeKey := currentPNPAllBarrierCandidateRouteKey
  status := currentPNPAllBarrierCandidateBarrierStatus
  worldInterfaces := currentPNPAllBarrierCandidateWorldInterfaces
  escapeLedger := currentPNPAllBarrierCandidateEscapeLedger

theorem currentPNPAllBarrierCandidateBarrierStatus_clears :
    currentPNPAllBarrierCandidateBarrierStatus.ClearsAll := by
  rfl

theorem currentPNPAllBarrierCandidateWorldInterfaces_missing :
    currentPNPAllBarrierCandidateWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPAllBarrierCandidateWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPAllBarrierCandidateWorldInterfaces.missingFor .algebrization =
        [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPAllBarrierCandidateWorldInterfaces_clears :
    currentPNPAllBarrierCandidateWorldInterfaces.ClearsAll := by
  exact currentPNPAllBarrierCandidateWorldInterfaces_missing

theorem currentPNPAllBarrierCandidateEscapeLedger_missing :
    currentPNPAllBarrierCandidateEscapeLedger.missingFor .relativization =
        [] ∧
      currentPNPAllBarrierCandidateEscapeLedger.missingFor .naturalProof =
        [] ∧
      currentPNPAllBarrierCandidateEscapeLedger.missingFor .algebrization =
        [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPAllBarrierCandidateEscapeLedger_clears :
    currentPNPAllBarrierCandidateEscapeLedger.ClearsAll := by
  exact currentPNPAllBarrierCandidateEscapeLedger_missing

theorem currentPNPAllBarrierCandidatePromotionGate_clears :
    currentPNPAllBarrierCandidatePromotionGate.ClearsAll := by
  exact
    ⟨currentPNPAllBarrierCandidateBarrierStatus_clears,
      currentPNPAllBarrierCandidateWorldInterfaces_clears,
      currentPNPAllBarrierCandidateEscapeLedger_clears⟩

theorem currentPNPBarrierSubsetFrontier_lab_positive_canary :
    currentPNPAllBarrierCandidatePromotionGate.ClearsAll ∧
      currentPNPAllBarrierCandidateWorldInterfaces.missingFor .relativization =
        [] ∧
      currentPNPAllBarrierCandidateWorldInterfaces.missingFor .naturalProof =
        [] ∧
      currentPNPAllBarrierCandidateWorldInterfaces.missingFor .algebrization =
        [] ∧
      currentPNPAllBarrierCandidateEscapeLedger.missingFor .relativization =
        [] ∧
      currentPNPAllBarrierCandidateEscapeLedger.missingFor .naturalProof =
        [] ∧
      currentPNPAllBarrierCandidateEscapeLedger.missingFor .algebrization =
        [] := by
  exact
    ⟨currentPNPAllBarrierCandidatePromotionGate_clears,
      currentPNPAllBarrierCandidateWorldInterfaces_missing.1,
      currentPNPAllBarrierCandidateWorldInterfaces_missing.2.1,
      currentPNPAllBarrierCandidateWorldInterfaces_missing.2.2,
      currentPNPAllBarrierCandidateEscapeLedger_missing.1,
      currentPNPAllBarrierCandidateEscapeLedger_missing.2.1,
      currentPNPAllBarrierCandidateEscapeLedger_missing.2.2⟩

theorem currentPNPBarrierSubsetFrontier_current_route_negative_canary :
    ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPKpolyPromotedWorldInterfaces.supplied = [] ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] := by
  exact
    ⟨(by
        intro hclears
        exact Bool.noConfusion hclears.1),
      currentPNPKpolyPromotedWorldInterfaces_supplied,
      currentPNPKpolyPromotedBarrierEscapeLedger_represented⟩

theorem currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary :
    ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll ∧
      ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll ∧
      ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll := by
  exact
    ⟨(by
        intro hclears
        exact Bool.noConfusion hclears.1),
      (by
        intro hclears
        exact Bool.noConfusion hclears.1),
      (by
        intro hclears
        exact Bool.noConfusion hclears.1),
      (by
        intro hclears
        exact Bool.noConfusion hclears.1),
      (by
        intro hclears
        exact Bool.noConfusion hclears.1),
      (by
        intro hclears
        exact Bool.noConfusion hclears.1)⟩

theorem currentPNPBarrierSubsetFrontier_lab_guardrails :
    currentPNPAllBarrierCandidatePromotionGate.ClearsAll ∧
      currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll ∧
      ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll ∧
      ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll ∧
      ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact
    ⟨currentPNPAllBarrierCandidatePromotionGate_clears,
      rfl,
      rfl,
      rfl,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.1,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.2.1,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.2.2.1,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.2.2.2.1,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.2.2.2.2.1,
      currentPNPBarrierSubsetFrontier_proper_subsets_negative_canary.2.2.2.2.2,
      currentPNPBarrierSubsetFrontier_current_route_negative_canary.1⟩

end Mettapedia.Computability.PNP
