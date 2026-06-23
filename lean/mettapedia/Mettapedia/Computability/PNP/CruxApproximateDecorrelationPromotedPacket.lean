import Mettapedia.Computability.PNP.CruxApproximateDecorrelationCoverage

/-!
# PNP approximate-decorrelation-promoted packet

This module records the packet-level effect of promoting the theorem-backed
approximate-decorrelation coverage surface.
-/

namespace Mettapedia.Computability.PNP

/-- The current local packet extended by the theorem-backed
approximate-decorrelation boundary.  At this point only the manuscript-specific
exact-visible / clocked `Kpoly` bridge remains outside the promoted packet. -/
def currentPNPApproximateDecorrelationPromotedPacket : PNPCruxPacket where
  covers
    | .approximateDecorrelation => ApproximateDecorrelationCoverage
    | repair => currentPNPRandomizedResidualPromotedPacket.covers repair

/-- Broad repair classes still open after promoting the theorem-backed
approximate-decorrelation packet. -/
def currentPNPApproximateDecorrelationPromotedUncoveredRepairClasses :
    List PNPRepairClass :=
  [.kpolyCompressionBridge]

/-- The approximate-decorrelation-promoted packet extends the
randomized-residual-promoted packet. -/
theorem currentPNPApproximateDecorrelationPromotedPacket_extends_randomizedResidualPromoted :
    currentPNPApproximateDecorrelationPromotedPacket.Extends
      currentPNPRandomizedResidualPromotedPacket := by
  intro repair hCurrent
  cases repair <;> try exact hCurrent
  case approximateDecorrelation =>
    cases hCurrent

/-- The approximate-decorrelation-promoted packet still covers the broad
residual-side-information repair class. -/
theorem residualSideInformation_covered_currentPNPApproximateDecorrelationPromotedPacket :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPRandomizedResidualPromotedPacket

/-- The approximate-decorrelation-promoted packet still covers the broad
randomized-residual repair class. -/
theorem randomizedResidual_covered_currentPNPApproximateDecorrelationPromotedPacket :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPRandomizedResidualPromotedPacket

/-- The approximate-decorrelation-promoted packet covers the broad
approximate-decorrelation repair class in the precise theorem-backed sense. -/
theorem approximateDecorrelation_covered_currentPNPApproximateDecorrelationPromotedPacket :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .approximateDecorrelation := by
  exact approximateDecorrelationCoverage

/-- Even after promoting the theorem-backed approximate-decorrelation layer,
the manuscript-specific `Kpoly` bridge remains outside the packet. -/
theorem kpolyCompressionBridge_uncovered_currentPNPApproximateDecorrelationPromotedPacket :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      .kpolyCompressionBridge := by
  simp [currentPNPApproximateDecorrelationPromotedPacket,
    currentPNPRandomizedResidualPromotedPacket,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The approximate-decorrelation-promoted packet is still not stop-grade
because the manuscript-specific `Kpoly` bridge remains open. -/
theorem not_stopGrade_currentPNPApproximateDecorrelationPromotedPacket :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.StopGrade := by
  intro hstop
  exact kpolyCompressionBridge_uncovered_currentPNPApproximateDecorrelationPromotedPacket
    (hstop .kpolyCompressionBridge)

/-- After promoting the approximate-decorrelation packet, the next broad gap is
the manuscript-specific `Kpoly` bridge. -/
def currentPNPApproximateDecorrelationPromotedNextMarginalTarget :
    PNPRepairClass :=
  .kpolyCompressionBridge

/-- The selected next target for the approximate-decorrelation-promoted packet
is still uncovered. -/
theorem currentPNPApproximateDecorrelationPromotedNextMarginalTarget_uncovered :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      currentPNPApproximateDecorrelationPromotedNextMarginalTarget := by
  simp [currentPNPApproximateDecorrelationPromotedNextMarginalTarget,
    currentPNPApproximateDecorrelationPromotedPacket,
    currentPNPRandomizedResidualPromotedPacket,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The selected next target for the approximate-decorrelation-promoted packet
is one of its remaining broad gaps. -/
theorem currentPNPApproximateDecorrelationPromotedNextMarginalTarget_mem_uncovered :
    currentPNPApproximateDecorrelationPromotedNextMarginalTarget ∈
      currentPNPApproximateDecorrelationPromotedUncoveredRepairClasses := by
  simp [currentPNPApproximateDecorrelationPromotedNextMarginalTarget,
    currentPNPApproximateDecorrelationPromotedUncoveredRepairClasses]

/-- Strongest honest status for the approximate-decorrelation-promoted packet:
the randomized-residual-promoted packet is extended, broad residual,
randomized-residual, and approximate-decorrelation repairs are now covered in
their theorem-backed senses, and only the manuscript-specific `Kpoly` bridge
remains open. -/
theorem currentPNPApproximateDecorrelationPromotedStatus :
    currentPNPApproximateDecorrelationPromotedPacket.Extends
        currentPNPRandomizedResidualPromotedPacket ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .residualSideInformation ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .randomizedResidual ∧
      currentPNPApproximateDecorrelationPromotedPacket.covers
        .approximateDecorrelation ∧
      ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
        .kpolyCompressionBridge ∧
      ¬ currentPNPApproximateDecorrelationPromotedPacket.StopGrade := by
  exact
    ⟨currentPNPApproximateDecorrelationPromotedPacket_extends_randomizedResidualPromoted,
      residualSideInformation_covered_currentPNPApproximateDecorrelationPromotedPacket,
      randomizedResidual_covered_currentPNPApproximateDecorrelationPromotedPacket,
      approximateDecorrelation_covered_currentPNPApproximateDecorrelationPromotedPacket,
      kpolyCompressionBridge_uncovered_currentPNPApproximateDecorrelationPromotedPacket,
      not_stopGrade_currentPNPApproximateDecorrelationPromotedPacket⟩

end Mettapedia.Computability.PNP
