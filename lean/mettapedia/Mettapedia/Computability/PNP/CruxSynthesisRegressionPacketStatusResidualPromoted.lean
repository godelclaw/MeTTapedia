import Mettapedia.Computability.PNP.CruxResidualPromotedPacket

/-!
# Regression checks for the residual-promoted PNP crux packet

Residual-side-information promoted-packet status wrappers extracted from the
historical packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_residual_promoted_packet_extends_current_regression :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket := by
  exact currentPNPResidualPromotedPacket_extends_current

theorem current_pnp_residual_promoted_packet_residual_side_information_covered_regression :
    currentPNPResidualPromotedPacket.covers .residualSideInformation := by
  exact residualSideInformation_covered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_randomized_residual_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual := by
  exact randomizedResidual_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation := by
  exact approximateDecorrelation_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge := by
  exact kpolyCompressionBridge_uncovered_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPResidualPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPResidualPromotedPacket

theorem current_pnp_residual_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPResidualPromotedPacket.covers
      currentPNPResidualPromotedNextMarginalTarget := by
  exact currentPNPResidualPromotedNextMarginalTarget_uncovered

theorem current_pnp_residual_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPResidualPromotedNextMarginalTarget ∈
      currentPNPResidualPromotedUncoveredRepairClasses := by
  exact currentPNPResidualPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_residual_promoted_packet_status_regression :
    currentPNPResidualPromotedPacket.Extends currentPNPLocalCruxPacket ∧
      currentPNPResidualPromotedPacket.covers .residualSideInformation ∧
      ¬ currentPNPResidualPromotedPacket.covers .randomizedResidual ∧
      ¬ currentPNPResidualPromotedPacket.covers .approximateDecorrelation ∧
      ¬ currentPNPResidualPromotedPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPResidualPromotedPacket.StopGrade := by
  exact currentPNPResidualPromotedStatus

end Mettapedia.Computability.PNP.CruxSynthesisRegression
