import Mettapedia.Computability.PNP.Barriers.ProperSubsetLabCanaries

/-!
# PNP barrier regression checks

Regression surface for the PNP cheap-falsification barrier layer.
-/

namespace Mettapedia.Computability.PNP.Barriers.Regression

open Mettapedia.Computability.PNP

theorem current_barrier_worlds_have_three_cases_regression :
    currentPNPBarrierChallengeWorlds.length = 3 := by
  exact currentPNPBarrierChallengeWorlds_length

theorem current_barrier_worlds_match_all_barriers_regression :
    PNPBarrierKind.all.map PNPBarrierKind.challengeWorld =
      currentPNPBarrierChallengeWorlds := by
  exact currentPNPBarrierChallengeWorlds_eq_all_barrier_worlds

theorem current_kpoly_promoted_route_not_barrier_cleared_regression :
    ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll := by
  exact currentPNPKpolyPromotedBarrierStatus_not_cleared

theorem current_kpoly_promoted_uncleared_barriers_regression :
    currentPNPKpolyPromotedBarrierStatus.unclearedBarriers =
      PNPBarrierKind.all := by
  exact currentPNPKpolyPromotedBarrierStatus_unclearedBarriers

theorem current_kpoly_promoted_missing_evidence_barriers_regression :
    currentPNPKpolyPromotedBarrierStatus.missingEvidenceBarriers =
      PNPBarrierKind.currentMissingEvidenceAfterAlgebrizationBlock := by
  exact currentPNPKpolyPromotedBarrierStatus_missingEvidenceBarriers

theorem current_kpoly_promoted_relativization_blocked_regression :
    currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears := by
  exact currentPNPKpolyPromotedRelativization_blocked_by_route_shape

theorem current_kpoly_promoted_natural_proof_blocked_regression :
    currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears := by
  exact currentPNPKpolyPromotedNaturalProof_blocked_by_route_shape

theorem current_kpoly_promoted_algebrization_blocked_regression :
    currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact currentPNPKpolyPromotedAlgebrization_blocked_by_route_shape

theorem current_kpoly_promoted_stop_grade_but_not_barrier_cleared_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_not_barrierCleared

theorem current_kpoly_promoted_stop_grade_but_missing_barrier_evidence_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.missingEvidenceBarriers =
        PNPBarrierKind.currentMissingEvidenceAfterAlgebrizationBlock := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_missingBarrierEvidence

theorem current_kpoly_promoted_stop_grade_but_relativization_blocked_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_relativizationBlocked

theorem current_kpoly_promoted_missing_oracle_challenge_world_generator_regression :
    PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_oracleChallengeWorldGenerator

theorem current_kpoly_promoted_oracle_challenge_world_generator_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_oracleChallengeWorldGenerator

theorem current_kpoly_promoted_missing_nonrelativizing_oracle_separation_regression :
    PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonrelativizingOracleSeparation

theorem current_kpoly_promoted_nonrelativizing_oracle_separation_not_represented_regression :
    ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact
    currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonrelativizingOracleSeparation

theorem current_kpoly_promoted_stop_grade_but_relativization_obstruction_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
      PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization ∧
      ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization ∧
      ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_relativizationObstruction

theorem current_kpoly_promoted_stop_grade_but_natural_proof_blocked_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofBlocked

theorem current_kpoly_promoted_missing_pseudorandom_sampler_regression :
    PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_pseudorandomChallengeWorldSampler

theorem current_kpoly_promoted_pseudorandom_sampler_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_pseudorandomChallengeWorldSampler

theorem current_kpoly_promoted_missing_natural_proof_audit_regression :
    PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_constructivityLargenessUsefulnessAudit

theorem current_kpoly_promoted_natural_proof_audit_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_constructivityLargenessUsefulnessAudit

theorem current_kpoly_promoted_missing_non_natural_escape_certificate_regression :
    PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_nonNaturalEscapeCertificate

theorem current_kpoly_promoted_non_natural_escape_certificate_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_nonNaturalEscapeCertificate

theorem current_kpoly_promoted_missing_non_natural_property_escape_regression :
    PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonNaturalPropertyEscape

theorem current_kpoly_promoted_non_natural_property_escape_not_represented_regression :
    ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonNaturalPropertyEscape

theorem current_kpoly_promoted_stop_grade_but_natural_proof_obstruction_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
      PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
      ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof ∧
      ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofObstruction

theorem current_kpoly_promoted_stop_grade_but_algebrization_blocked_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationBlocked

theorem current_kpoly_promoted_missing_algebraic_oracle_generator_regression :
    PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleChallengeWorldGenerator

theorem current_kpoly_promoted_algebraic_oracle_generator_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleChallengeWorldGenerator

theorem current_kpoly_promoted_missing_algebraic_lift_interface_regression :
    PNPBarrierWorldInterface.algebraicLiftInterface ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_algebraicLiftInterface

theorem current_kpoly_promoted_algebraic_lift_interface_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicLiftInterface

theorem current_kpoly_promoted_missing_algebraic_oracle_invariant_claim_regression :
    PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleInvariantSeparationClaim

theorem current_kpoly_promoted_algebraic_oracle_invariant_claim_not_supplied_regression :
    ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleInvariantSeparationClaim

theorem current_kpoly_promoted_missing_non_algebrizing_oracle_separation_regression :
    PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonAlgebrizingAlgebraicOracleSeparation

theorem current_kpoly_promoted_non_algebrizing_oracle_separation_not_represented_regression :
    ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact
    currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonAlgebrizingAlgebraicOracleSeparation

theorem current_kpoly_promoted_stop_grade_but_algebrization_obstruction_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears ∧
      PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.algebraicLiftInterface ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
        currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
      ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
        currentPNPKpolyPromotedWorldInterfaces.supplied ∧
      PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization ∧
      ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
        currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationObstruction

theorem current_kpoly_promoted_stop_grade_but_all_barrier_obstructions_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      (currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
        ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
        PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization ∧
        ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization ∧
        ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      (currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
        ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
        PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof ∧
        ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof ∧
        ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      (currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
        ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears ∧
        PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.algebraicLiftInterface ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
          currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization ∧
        ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
          currentPNPKpolyPromotedWorldInterfaces.supplied ∧
        PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization ∧
        ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
          currentPNPKpolyPromotedBarrierEscapeLedger.represented) ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_allBarrierObstructions

theorem replacement_gate_requires_all_obligations_regression
    {gate : PNPBarrierPromotionGate}
    (hclears : gate.ClearsAll) :
    (gate.status.relativization = .cleared ∧
      gate.status.naturalProof = .cleared ∧
      gate.status.algebrization = .cleared) ∧
      (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
        requirement ∈ kind.requiredWorldInterfaces →
          requirement ∈ gate.worldInterfaces.supplied) ∧
      (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
        witness ∈ kind.requiredEscapeWitnesses →
          witness ∈ gate.escapeLedger.represented) := by
  exact
    PNPBarrierPromotionGate.clearsAll_requires_replacement_obligations hclears

theorem current_kpoly_promoted_replacement_gate_obligations_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      (∀ {gate : PNPBarrierPromotionGate},
        gate.ClearsAll →
          (gate.status.relativization = .cleared ∧
            gate.status.naturalProof = .cleared ∧
            gate.status.algebrization = .cleared) ∧
          (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
            requirement ∈ kind.requiredWorldInterfaces →
              requirement ∈ gate.worldInterfaces.supplied) ∧
          (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
            witness ∈ kind.requiredEscapeWitnesses →
              witness ∈ gate.escapeLedger.represented)) ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_replacement_gate_obligations

theorem relativization_only_candidate_clears_relativization_but_not_promotion_regression :
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
  exact currentPNPRelativizationOnlyCandidate_clears_relativization_but_not_promotion

theorem natural_proof_only_candidate_clears_naturalProof_but_not_promotion_regression :
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
  exact currentPNPNaturalProofOnlyCandidate_clears_naturalProof_but_not_promotion

theorem algebrization_only_candidate_clears_algebrization_but_not_promotion_regression :
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
  exact currentPNPAlgebrizationOnlyCandidate_clears_algebrization_but_not_promotion

theorem one_barrier_candidate_gates_all_fail_promotion_regression :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPOneBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact currentPNPOneBarrierCandidatePromotionGates_length_and_all_fail_promotion

theorem one_barrier_frontier_single_layer_clearances_fail_promotion_regression :
    (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
      ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) := by
  exact currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion

theorem two_barrier_candidate_gates_all_fail_promotion_regression :
    currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPTwoBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact currentPNPTwoBarrierCandidatePromotionGates_length_and_all_fail_promotion

theorem two_barrier_frontier_double_layer_clearances_fail_promotion_regression :
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
  exact currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion

theorem proper_subset_barrier_candidate_gates_all_fail_promotion_regression :
    currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      (∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact
    ⟨currentPNPProperSubsetBarrierCandidatePromotionGates_length,
      currentPNPProperSubsetBarrierCandidatePromotionGates_all_fail_promotion⟩

theorem proper_subset_barrier_frontier_all_strict_subsets_fail_promotion_regression :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      (∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) ∧
      (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
        ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) ∧
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
    currentPNPProperSubsetBarrierFrontier_all_strict_subsets_fail_promotion

theorem barrier_subset_all_three_bool_canary_regression :
    pnpBarrierSubsetAllThreeCanaryAudit.verdictLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.worldInterfaceLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.escapeWitnessLayerClears = true ∧
      pnpBarrierSubsetAllThreeCanaryAudit.clearsGlobalPromotionGate = true := by
  exact pnpBarrierSubsetAllThree_lab_positive_canary

theorem barrier_subset_current_local_ledger_bool_canary_regression :
    pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.verdictLayerClears = false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.worldInterfaceLayerClears =
        false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.escapeWitnessLayerClears =
        false ∧
      pnpBarrierSubsetCurrentLocalLedgerCanaryAudit.clearsGlobalPromotionGate =
        false := by
  exact pnpBarrierSubsetCurrentLocalLedger_negative_canary

theorem barrier_subset_proper_subsets_bool_canary_regression :
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
  exact pnpBarrierSubsetProperSubsets_negative_canary

theorem barrier_subset_frontier_bool_guardrails_regression :
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
  exact pnpBarrierSubsetFrontierCanaries_guardrails

theorem all_barrier_candidate_clears_promotion_gate_regression :
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
  exact currentPNPBarrierSubsetFrontier_lab_positive_canary

theorem current_barrier_subset_frontier_current_route_negative_regression :
    ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPKpolyPromotedWorldInterfaces.supplied = [] ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] := by
  exact currentPNPBarrierSubsetFrontier_current_route_negative_canary

theorem barrier_subset_frontier_lab_guardrails_regression :
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
  exact currentPNPBarrierSubsetFrontier_lab_guardrails

theorem current_kpoly_promoted_stop_grade_but_all_barriers_blocked_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_allBarriersBlocked

theorem current_kpoly_promoted_world_interfaces_empty_regression :
    currentPNPKpolyPromotedWorldInterfaces.supplied = [] := by
  exact currentPNPKpolyPromotedWorldInterfaces_supplied

theorem current_kpoly_promoted_escape_witnesses_empty_regression :
    currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_represented

theorem current_kpoly_promoted_missing_relativization_world_interfaces_regression :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization =
      PNPBarrierKind.relativization.requiredWorldInterfaces := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_relativization

theorem current_kpoly_promoted_missing_natural_proof_world_interfaces_regression :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredWorldInterfaces := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_naturalProof

theorem current_kpoly_promoted_missing_algebrization_world_interfaces_regression :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  exact currentPNPKpolyPromotedWorldInterfaces_missing_algebrization

theorem current_kpoly_promoted_missing_relativization_escape_witnesses_regression :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization =
      PNPBarrierKind.relativization.requiredEscapeWitnesses := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_relativization

theorem current_kpoly_promoted_missing_natural_proof_escape_witnesses_regression :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredEscapeWitnesses := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_naturalProof

theorem current_kpoly_promoted_missing_algebrization_escape_witnesses_regression :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredEscapeWitnesses := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_missing_algebrization

theorem current_kpoly_promoted_escape_witness_layer_not_cleared_regression :
    ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll := by
  exact currentPNPKpolyPromotedBarrierEscapeLedger_not_cleared

theorem current_kpoly_promoted_world_interface_layer_not_cleared_regression :
    ¬ currentPNPKpolyPromotedWorldInterfaces.ClearsAll := by
  exact currentPNPKpolyPromotedWorldInterfaces_not_cleared

theorem current_kpoly_promoted_promotion_gate_not_cleared_regression :
    ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedBarrierPromotionGate_not_cleared

theorem current_kpoly_promoted_stop_grade_but_world_interface_packet_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedWorldInterfaces.supplied = [] ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_worldInterface_packet

theorem current_kpoly_promoted_stop_grade_but_escape_witness_packet_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_escapeWitness_packet

theorem current_kpoly_promoted_stop_grade_but_promotion_gate_refuted_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll ∧
      ¬ currentPNPKpolyPromotedWorldInterfaces.ClearsAll ∧
      ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact currentPNPKpolyPromotedPacket_stopGrade_and_promotionGate_refuted

end Mettapedia.Computability.PNP.Barriers.Regression
