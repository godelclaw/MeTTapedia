import Mettapedia.Computability.PNP.CruxRandomizedResidualPromotedPacket

/-!
# Regression checks for the randomized-residual promoted PNP crux packet

Randomized-residual promoted-packet status wrappers extracted from the
historical packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_randomized_residual_promoted_packet_extends_residual_promoted_regression :
    currentPNPRandomizedResidualPromotedPacket.Extends
      currentPNPResidualPromotedPacket := by
  exact currentPNPRandomizedResidualPromotedPacket_extends_residualPromoted

theorem current_pnp_randomized_residual_promoted_packet_residual_side_information_covered_regression :
    currentPNPRandomizedResidualPromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_randomized_residual_covered_regression :
    currentPNPRandomizedResidualPromotedPacket.covers .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_uncovered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_uncovered_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPRandomizedResidualPromotedPacket

theorem current_pnp_randomized_residual_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPRandomizedResidualPromotedPacket.covers
      currentPNPRandomizedResidualPromotedNextMarginalTarget := by
  exact currentPNPRandomizedResidualPromotedNextMarginalTarget_uncovered

theorem current_pnp_randomized_residual_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPRandomizedResidualPromotedNextMarginalTarget ∈
      currentPNPRandomizedResidualPromotedUncoveredRepairClasses := by
  exact currentPNPRandomizedResidualPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_randomized_residual_promoted_packet_status_regression :
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
  exact currentPNPRandomizedResidualPromotedStatus

end Mettapedia.Computability.PNP.CruxSynthesisRegression
