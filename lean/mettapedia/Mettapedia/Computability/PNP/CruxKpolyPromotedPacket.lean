import Mettapedia.Computability.PNP.CruxKpolyCompressionBridgeCoverageCore
import Mettapedia.Computability.PNP.CruxApproximateDecorrelationPromotedPacket

/-!
# PNP `Kpoly`-promoted packet

Final packet/status layer after theorem-backed `Kpoly` compression-bridge
coverage is added to the approximate-decorrelation-promoted packet.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The current local packet extended by the theorem-backed blocker for the
manuscript's remaining `Kpoly` bridge-from-product-success route.  This closes
the current broad PNP ledger. -/
def currentPNPKpolyCompressionBridgePromotedPacket : PNPCruxPacket where
  covers
    | .kpolyCompressionBridge => KpolyCompressionBridgeCoverage
    | repair => currentPNPApproximateDecorrelationPromotedPacket.covers repair

/-- The `Kpoly`-bridge-promoted packet extends the
approximate-decorrelation-promoted packet. -/
theorem currentPNPKpolyCompressionBridgePromotedPacket_extends_approximateDecorrelationPromoted :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
      currentPNPApproximateDecorrelationPromotedPacket := by
  intro repair hCurrent
  cases repair <;> try exact hCurrent
  case kpolyCompressionBridge =>
    cases hCurrent

/-- The `Kpoly`-bridge-promoted packet extends the baseline current packet. -/
theorem currentPNPKpolyCompressionBridgePromotedPacket_extends_current :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
      currentPNPLocalCruxPacket := by
  intro repair hCurrent
  exact
    currentPNPKpolyCompressionBridgePromotedPacket_extends_approximateDecorrelationPromoted
      repair
      (currentPNPApproximateDecorrelationPromotedPacket_extends_randomizedResidualPromoted
        repair
        (currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted
          repair
          (currentPNPResidualPromotedPacket_extends_current repair hCurrent)))

/-- The `Kpoly`-bridge-promoted packet still covers the broad
residual-side-information repair class. -/
theorem residualSideInformation_covered_currentPNPKpolyCompressionBridgePromotedPacket :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPApproximateDecorrelationPromotedPacket

/-- The `Kpoly`-bridge-promoted packet still covers the broad randomized
residual repair class. -/
theorem randomizedResidual_covered_currentPNPKpolyCompressionBridgePromotedPacket :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPApproximateDecorrelationPromotedPacket

/-- The `Kpoly`-bridge-promoted packet still covers the broad
approximate-decorrelation repair class. -/
theorem approximateDecorrelation_covered_currentPNPKpolyCompressionBridgePromotedPacket :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_covered_currentPNPApproximateDecorrelationPromotedPacket

/-- The `Kpoly`-bridge-promoted packet covers the remaining broad bridge class
in the precise theorem-backed route-blocking sense. -/
theorem kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .kpolyCompressionBridge := by
  exact kpolyCompressionBridgeCoverage

/-- The `Kpoly`-bridge-promoted packet covers the original current gap list. -/
theorem currentPNPKpolyCompressionBridgePromotedPacket_covers_current_gaps :
    currentPNPKpolyCompressionBridgePromotedPacket.CoversList
      currentPNPUncoveredRepairClasses := by
  intro repair hrepair
  simp [currentPNPUncoveredRepairClasses] at hrepair
  rcases hrepair with rfl | rfl | rfl | rfl
  · exact residualSideInformation_covered_currentPNPKpolyCompressionBridgePromotedPacket
  · exact randomizedResidual_covered_currentPNPKpolyCompressionBridgePromotedPacket
  · exact approximateDecorrelation_covered_currentPNPKpolyCompressionBridgePromotedPacket
  · exact kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket

/-- The `Kpoly`-bridge-promoted packet is stop-grade for the current PNP
ledger. -/
theorem stopGrade_currentPNPKpolyCompressionBridgePromotedPacket :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade := by
  intro repair
  by_cases hCurrent : currentPNPLocalCruxPacket.covers repair
  · exact
      currentPNPKpolyCompressionBridgePromotedPacket_extends_current
        repair hCurrent
  · exact
      currentPNPKpolyCompressionBridgePromotedPacket_covers_current_gaps
        repair ((currentPNPUncoveredRepairClasses_exact repair).2 hCurrent)

/-- Strongest honest status for the `Kpoly`-bridge-promoted packet: the
approximate-decorrelation-promoted packet is extended, all currently named
broad PNP repair classes are covered in theorem-backed form, and the packet is
therefore stop-grade for this ledger. -/
theorem currentPNPKpolyCompressionBridgePromotedStatus :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
        currentPNPApproximateDecorrelationPromotedPacket ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .residualSideInformation ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .randomizedResidual ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .approximateDecorrelation ∧
      currentPNPKpolyCompressionBridgePromotedPacket.covers
        .kpolyCompressionBridge ∧
      currentPNPKpolyCompressionBridgePromotedPacket.StopGrade := by
  exact
    ⟨currentPNPKpolyCompressionBridgePromotedPacket_extends_approximateDecorrelationPromoted,
      residualSideInformation_covered_currentPNPKpolyCompressionBridgePromotedPacket,
      randomizedResidual_covered_currentPNPKpolyCompressionBridgePromotedPacket,
      approximateDecorrelation_covered_currentPNPKpolyCompressionBridgePromotedPacket,
      kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket,
      stopGrade_currentPNPKpolyCompressionBridgePromotedPacket⟩

end Mettapedia.Computability.PNP
