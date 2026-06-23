import Mettapedia.Computability.PNP.CruxRandomizedResidualCoverageV13
import Mettapedia.Computability.PNP.CruxRandomizedResidualCoverageBroad
import Mettapedia.Computability.PNP.CruxResidualPromotedPacket

/-!
# PNP randomized-residual-promoted packet

This module records the packet-level effect of promoting the theorem-backed
randomized-residual coverage surface.
-/

namespace Mettapedia.Computability.PNP

/-- The residual-promoted packet further extended by the fully theorem-backed
randomized-residual collapse to deterministic coin-slice obstructions.  This
still leaves the approximate-decorrelation and manuscript-specific `Kpoly`
bridge repairs open. -/
def currentPNPRandomizedResidualPromotedPacket : PNPCruxPacket where
  covers
    | .randomizedResidual => RandomizedResidualCoverage
    | repair => currentPNPResidualPromotedPacket.covers repair

/-- Broad repair classes still open after promoting the theorem-backed
randomized-residual packet. -/
def currentPNPRandomizedResidualPromotedUncoveredRepairClasses :
    List PNPRepairClass :=
  [.approximateDecorrelation, .kpolyCompressionBridge]

/-- The randomized-residual-promoted packet extends the
residual-side-information-promoted packet. -/
theorem currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted :
    currentPNPRandomizedResidualPromotedPacket.Extends
      currentPNPResidualPromotedPacket := by
  intro repair hCurrent
  cases repair <;> try exact hCurrent
  case randomizedResidual =>
    cases hCurrent

/-- The randomized-residual-promoted packet still covers the broad
residual-side-information repair class. -/
theorem residualSideInformation_covered_currentPNPRandomizedResidualPromotedPacket :
    currentPNPRandomizedResidualPromotedPacket.covers
      .residualSideInformation := by
  exact
    currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted
      .residualSideInformation
      residualSideInformation_covered_currentPNPResidualPromotedPacket

/-- The randomized-residual-promoted packet covers the broad randomized-
residual repair class. -/
theorem randomizedResidual_covered_currentPNPRandomizedResidualPromotedPacket :
    currentPNPRandomizedResidualPromotedPacket.covers .randomizedResidual := by
  exact randomizedResidualCoverage

/-- Approximate-decorrelation repairs remain outside the randomized-residual-
promoted packet. -/
theorem approximateDecorrelation_uncovered_currentPNPRandomizedResidualPromotedPacket :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .approximateDecorrelation := by
  simp [currentPNPRandomizedResidualPromotedPacket,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The manuscript-specific `Kpoly` bridge remains outside the
randomized-residual-promoted packet. -/
theorem kpolyCompressionBridge_uncovered_currentPNPRandomizedResidualPromotedPacket :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .kpolyCompressionBridge := by
  simp [currentPNPRandomizedResidualPromotedPacket,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The randomized-residual-promoted packet is still not stop-grade because
approximate-decorrelation repairs remain open. -/
theorem not_stopGrade_currentPNPRandomizedResidualPromotedPacket :
    ¬ currentPNPRandomizedResidualPromotedPacket.StopGrade := by
  intro hstop
  exact approximateDecorrelation_uncovered_currentPNPRandomizedResidualPromotedPacket
    (hstop .approximateDecorrelation)

/-- After promoting the randomized-residual packet, the next broad gap is the
approximate-decorrelation route. -/
def currentPNPRandomizedResidualPromotedNextMarginalTarget : PNPRepairClass :=
  .approximateDecorrelation

/-- The selected next target for the randomized-residual-promoted packet is
still uncovered. -/
theorem currentPNPRandomizedResidualPromotedNextMarginalTarget_uncovered :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      currentPNPRandomizedResidualPromotedNextMarginalTarget := by
  simp [currentPNPRandomizedResidualPromotedNextMarginalTarget,
    currentPNPRandomizedResidualPromotedPacket,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The selected next target for the randomized-residual-promoted packet is
one of its remaining broad gaps. -/
theorem currentPNPRandomizedResidualPromotedNextMarginalTarget_mem_uncovered :
    currentPNPRandomizedResidualPromotedNextMarginalTarget ∈
      currentPNPRandomizedResidualPromotedUncoveredRepairClasses := by
  simp [currentPNPRandomizedResidualPromotedNextMarginalTarget,
    currentPNPRandomizedResidualPromotedUncoveredRepairClasses]

/-- Strongest honest status for the randomized-residual-promoted packet: the
residual-side-information-promoted packet is extended, broad randomized
residual repairs are now covered in their theorem-backed sense, but
approximate decorrelation and the manuscript-specific `Kpoly` bridge remain
open. -/
theorem currentPNPRandomizedResidualPromotedStatus :
    currentPNPRandomizedResidualPromotedPacket.Extends
        currentPNPResidualPromotedPacket ∧
      currentPNPRandomizedResidualPromotedPacket.covers
        .residualSideInformation ∧
      currentPNPRandomizedResidualPromotedPacket.covers .randomizedResidual ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.covers
        .approximateDecorrelation ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.covers
        .kpolyCompressionBridge ∧
      ¬ currentPNPRandomizedResidualPromotedPacket.StopGrade := by
  exact
    ⟨currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted,
      residualSideInformation_covered_currentPNPRandomizedResidualPromotedPacket,
      randomizedResidual_covered_currentPNPRandomizedResidualPromotedPacket,
      approximateDecorrelation_uncovered_currentPNPRandomizedResidualPromotedPacket,
      kpolyCompressionBridge_uncovered_currentPNPRandomizedResidualPromotedPacket,
      not_stopGrade_currentPNPRandomizedResidualPromotedPacket⟩

end Mettapedia.Computability.PNP
