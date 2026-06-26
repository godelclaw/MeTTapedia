import Mettapedia.Computability.PNP.Barriers.NaturalProofObstruction

/-!
# PNP algebrization obstruction

This module makes the current Kpoly-promoted route's algebrization obstruction
first-class: the route is locally stop-grade, but it supplies neither the
algebraic-oracle challenge-world interfaces nor the positive non-algebrizing
escape witness needed before a global PNP route could claim to pass
algebrization.
-/

namespace Mettapedia.Computability.PNP

theorem currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleChallengeWorldGenerator :
    PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleChallengeWorldGenerator :
    ¬ PNPBarrierWorldInterface.algebraicOracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleChallengeWorldGenerator

theorem currentPNPKpolyPromotedWorldInterfaces_missing_algebraicLiftInterface :
    PNPBarrierWorldInterface.algebraicLiftInterface ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicLiftInterface :
    ¬ PNPBarrierWorldInterface.algebraicLiftInterface ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicLiftInterface

theorem currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleInvariantSeparationClaim :
    PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleInvariantSeparationClaim :
    ¬ PNPBarrierWorldInterface.algebraicOracleInvariantSeparationClaim ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleInvariantSeparationClaim

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonAlgebrizingAlgebraicOracleSeparation :
    PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonAlgebrizingAlgebraicOracleSeparation :
    ¬ PNPBarrierEscapeWitness.nonAlgebrizingAlgebraicOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact
    PNPBarrierEscapeLedger.not_represented_of_mem_missingFor
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonAlgebrizingAlgebraicOracleSeparation

/-- The current Kpoly-promoted route is locally stop-grade, but its
algebrization layer lacks the algebraic-oracle challenge-world interfaces and
the positive non-algebrizing escape witness. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationObstruction :
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
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      (currentPNPKpolyPromotedAlgebrization_blocked_by_route_shape).1,
      (currentPNPKpolyPromotedAlgebrization_blocked_by_route_shape).2,
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleChallengeWorldGenerator,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleChallengeWorldGenerator,
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicLiftInterface,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicLiftInterface,
      currentPNPKpolyPromotedWorldInterfaces_missing_algebraicOracleInvariantSeparationClaim,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_algebraicOracleInvariantSeparationClaim,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonAlgebrizingAlgebraicOracleSeparation,
      currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonAlgebrizingAlgebraicOracleSeparation⟩

end Mettapedia.Computability.PNP
