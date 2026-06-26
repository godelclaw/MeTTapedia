import Mettapedia.Computability.PNP.Barriers.Basic

/-!
# PNP relativization obstruction

This module makes the current Kpoly-promoted route's relativization obstruction
first-class: the route is locally stop-grade, but it supplies neither the
oracle challenge-world interface nor the nonrelativizing escape witness needed
before a global PNP route could claim to pass relativization.
-/

namespace Mettapedia.Computability.PNP

/-- A missing barrier-world interface has not been supplied by the route. -/
theorem PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
    {interfaces : PNPBarrierRouteWorldInterfaces}
    {kind : PNPBarrierKind}
    {requirement : PNPBarrierWorldInterface}
    (h : requirement ∈ interfaces.missingFor kind) :
    ¬ requirement ∈ interfaces.supplied := by
  have h' : requirement ∈ kind.requiredWorldInterfaces ∧
      requirement ∉ interfaces.supplied := by
    simpa [PNPBarrierRouteWorldInterfaces.missingFor] using h
  exact h'.2

/-- A missing barrier-world interface is required by the corresponding barrier. -/
theorem PNPBarrierRouteWorldInterfaces.required_of_mem_missingFor
    {interfaces : PNPBarrierRouteWorldInterfaces}
    {kind : PNPBarrierKind}
    {requirement : PNPBarrierWorldInterface}
    (h : requirement ∈ interfaces.missingFor kind) :
    requirement ∈ kind.requiredWorldInterfaces := by
  have h' : requirement ∈ kind.requiredWorldInterfaces ∧
      requirement ∉ interfaces.supplied := by
    simpa [PNPBarrierRouteWorldInterfaces.missingFor] using h
  exact h'.1

/-- A missing positive escape witness has not been represented by the route. -/
theorem PNPBarrierEscapeLedger.not_represented_of_mem_missingFor
    {ledger : PNPBarrierEscapeLedger}
    {kind : PNPBarrierKind}
    {witness : PNPBarrierEscapeWitness}
    (h : witness ∈ ledger.missingFor kind) :
    ¬ witness ∈ ledger.represented := by
  have h' : witness ∈ kind.requiredEscapeWitnesses ∧
      witness ∉ ledger.represented := by
    simpa [PNPBarrierEscapeLedger.missingFor] using h
  exact h'.2

/-- A missing positive escape witness is required by the corresponding barrier. -/
theorem PNPBarrierEscapeLedger.required_of_mem_missingFor
    {ledger : PNPBarrierEscapeLedger}
    {kind : PNPBarrierKind}
    {witness : PNPBarrierEscapeWitness}
    (h : witness ∈ ledger.missingFor kind) :
    witness ∈ kind.requiredEscapeWitnesses := by
  have h' : witness ∈ kind.requiredEscapeWitnesses ∧
      witness ∉ ledger.represented := by
    simpa [PNPBarrierEscapeLedger.missingFor] using h
  exact h'.1

theorem currentPNPKpolyPromotedWorldInterfaces_missing_oracleChallengeWorldGenerator :
    PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_oracleChallengeWorldGenerator :
    ¬ PNPBarrierWorldInterface.oracleChallengeWorldGenerator ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_oracleChallengeWorldGenerator

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonrelativizingOracleSeparation :
    PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonrelativizingOracleSeparation :
    ¬ PNPBarrierEscapeWitness.nonrelativizingOracleSeparation ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact
    PNPBarrierEscapeLedger.not_represented_of_mem_missingFor
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonrelativizingOracleSeparation

/-- The current Kpoly-promoted route is locally stop-grade, but its
relativization layer lacks both the oracle-world interface and the positive
nonrelativizing escape witness. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_relativizationObstruction :
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
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      (currentPNPKpolyPromotedRelativization_blocked_by_route_shape).1,
      (currentPNPKpolyPromotedRelativization_blocked_by_route_shape).2,
      currentPNPKpolyPromotedWorldInterfaces_missing_oracleChallengeWorldGenerator,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_oracleChallengeWorldGenerator,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonrelativizingOracleSeparation,
      currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonrelativizingOracleSeparation⟩

end Mettapedia.Computability.PNP
