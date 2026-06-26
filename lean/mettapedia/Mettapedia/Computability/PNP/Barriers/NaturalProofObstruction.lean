import Mettapedia.Computability.PNP.Barriers.RelativizationObstruction

/-!
# PNP natural-proofs obstruction

This module makes the current Kpoly-promoted route's natural-proofs obstruction
first-class: the route is locally stop-grade, but it supplies neither the
pseudorandom challenge-world interfaces nor the positive non-natural escape
witness needed before a global PNP route could claim to pass natural proofs.
-/

namespace Mettapedia.Computability.PNP

theorem currentPNPKpolyPromotedWorldInterfaces_missing_pseudorandomChallengeWorldSampler :
    PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_pseudorandomChallengeWorldSampler :
    ¬ PNPBarrierWorldInterface.pseudorandomChallengeWorldSampler ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_pseudorandomChallengeWorldSampler

theorem currentPNPKpolyPromotedWorldInterfaces_missing_constructivityLargenessUsefulnessAudit :
    PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_constructivityLargenessUsefulnessAudit :
    ¬ PNPBarrierWorldInterface.constructivityLargenessUsefulnessAudit ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_constructivityLargenessUsefulnessAudit

theorem currentPNPKpolyPromotedWorldInterfaces_missing_nonNaturalEscapeCertificate :
    PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_supplied_nonNaturalEscapeCertificate :
    ¬ PNPBarrierWorldInterface.nonNaturalEscapeCertificate ∈
      currentPNPKpolyPromotedWorldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentPNPKpolyPromotedWorldInterfaces_missing_nonNaturalEscapeCertificate

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonNaturalPropertyEscape :
    PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonNaturalPropertyEscape :
    ¬ PNPBarrierEscapeWitness.nonNaturalPropertyEscape ∈
      currentPNPKpolyPromotedBarrierEscapeLedger.represented := by
  exact
    PNPBarrierEscapeLedger.not_represented_of_mem_missingFor
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonNaturalPropertyEscape

/-- The current Kpoly-promoted route is locally stop-grade, but its
natural-proofs layer lacks the pseudorandom challenge-world interfaces and the
positive non-natural escape witness. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofObstruction :
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
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      (currentPNPKpolyPromotedNaturalProof_blocked_by_route_shape).1,
      (currentPNPKpolyPromotedNaturalProof_blocked_by_route_shape).2,
      currentPNPKpolyPromotedWorldInterfaces_missing_pseudorandomChallengeWorldSampler,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_pseudorandomChallengeWorldSampler,
      currentPNPKpolyPromotedWorldInterfaces_missing_constructivityLargenessUsefulnessAudit,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_constructivityLargenessUsefulnessAudit,
      currentPNPKpolyPromotedWorldInterfaces_missing_nonNaturalEscapeCertificate,
      currentPNPKpolyPromotedWorldInterfaces_not_supplied_nonNaturalEscapeCertificate,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_nonNaturalPropertyEscape,
      currentPNPKpolyPromotedBarrierEscapeLedger_not_represented_nonNaturalPropertyEscape⟩

end Mettapedia.Computability.PNP
