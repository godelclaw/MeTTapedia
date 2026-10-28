import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageV13
import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageBroad
import Mettapedia.Computability.PNP.CruxLocalPacketStatus

/-!
# PNP residual-promoted packet

This module records the packet-level effect of promoting the theorem-backed
residual-side-information coverage surface.
-/

namespace Mettapedia.Computability.PNP

/-- The current local packet extended only by the fully theorem-backed
residual-side-information obstruction layer.  This still leaves the randomized
residual, approximate-decorrelation, and manuscript-specific `Kpoly` bridge
repairs open. -/
def currentPNPResidualPromotedPacket : PNPCruxPacket where
  covers
    | .residualSideInformation => ResidualSideInformationCoverage
    | repair => currentPNPLocalCruxPacket.covers repair

/-- Broad repair classes covered by the residual-promoted packet. -/
def currentPNPResidualPromotedCoveredRepairClasses : List PNPRepairClass :=
  currentPNPCoveredRepairClasses ++ [.residualSideInformation]

/-- Broad repair classes still open after promoting the theorem-backed
residual-side-information packet. -/
def currentPNPResidualPromotedUncoveredRepairClasses : List PNPRepairClass :=
  [.randomizedResidual,
    .approximateDecorrelation,
    .kpolyCompressionBridge]

/-- The residual-promoted packet extends the current local packet. -/
theorem currentPNPResidualPromotedPacket_extends_current :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket := by
  intro repair hCurrent
  cases repair <;> try exact hCurrent
  case residualSideInformation =>
    cases hCurrent

/-- The residual-promoted packet covers the broad residual-side-information
repair class. -/
theorem residualSideInformation_covered_currentPNPResidualPromotedPacket :
    currentPNPResidualPromotedPacket.covers .residualSideInformation := by
  exact residualSideInformationCoverage

/-- Even after promoting the theorem-backed residual-side-information layer,
randomized residual repairs remain outside the packet. -/
theorem randomizedResidual_uncovered_currentPNPResidualPromotedPacket :
    ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual := by
  simp [currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- Approximate-decorrelation repairs remain outside the residual-promoted
packet. -/
theorem approximateDecorrelation_uncovered_currentPNPResidualPromotedPacket :
    ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation := by
  simp [currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The manuscript-specific `Kpoly` bridge remains outside the
residual-promoted packet. -/
theorem kpolyCompressionBridge_uncovered_currentPNPResidualPromotedPacket :
    ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge := by
  simp [currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The residual-promoted packet is still not stop-grade because randomized
residual repairs remain open. -/
theorem not_stopGrade_currentPNPResidualPromotedPacket :
    ¬ currentPNPResidualPromotedPacket.StopGrade := by
  intro hstop
  exact randomizedResidual_uncovered_currentPNPResidualPromotedPacket
    (hstop .randomizedResidual)

/-- After promoting the residual-side-information packet, the next broad gap is
the randomized residual route. -/
def currentPNPResidualPromotedNextMarginalTarget : PNPRepairClass :=
  .randomizedResidual

/-- The selected next target for the residual-promoted packet is still
uncovered. -/
theorem currentPNPResidualPromotedNextMarginalTarget_uncovered :
    ¬ currentPNPResidualPromotedPacket.covers
      currentPNPResidualPromotedNextMarginalTarget := by
  simp [currentPNPResidualPromotedNextMarginalTarget,
    currentPNPResidualPromotedPacket, currentPNPLocalCruxPacket]

/-- The selected next target for the residual-promoted packet is one of its
remaining broad gaps. -/
theorem currentPNPResidualPromotedNextMarginalTarget_mem_uncovered :
    currentPNPResidualPromotedNextMarginalTarget ∈
      currentPNPResidualPromotedUncoveredRepairClasses := by
  simp [currentPNPResidualPromotedNextMarginalTarget,
    currentPNPResidualPromotedUncoveredRepairClasses]

/-- Strongest honest status for the residual-promoted packet: the current local
packet is extended, broad residual-side-information repairs are now covered in
their theorem-backed sense, but randomized residual, approximate decorrelation,
and the manuscript-specific `Kpoly` bridge remain open. -/
theorem currentPNPResidualPromotedStatus :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket ∧
      currentPNPResidualPromotedPacket.covers .residualSideInformation ∧
      ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual ∧
      ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation ∧
      ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPResidualPromotedPacket.StopGrade := by
  exact
    ⟨currentPNPResidualPromotedPacket_extends_current,
      residualSideInformation_covered_currentPNPResidualPromotedPacket,
      randomizedResidual_uncovered_currentPNPResidualPromotedPacket,
      approximateDecorrelation_uncovered_currentPNPResidualPromotedPacket,
      kpolyCompressionBridge_uncovered_currentPNPResidualPromotedPacket,
      not_stopGrade_currentPNPResidualPromotedPacket⟩

end Mettapedia.Computability.PNP
