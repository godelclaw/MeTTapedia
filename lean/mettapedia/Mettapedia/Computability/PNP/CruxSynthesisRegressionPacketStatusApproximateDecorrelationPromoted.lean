import Mettapedia.Computability.PNP.CruxApproximateDecorrelationPromotedPacket

/-!
# Regression checks for the approximate-decorrelation promoted PNP crux packet

Approximate-decorrelation promoted-packet status wrappers extracted from the
historical packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_approximate_decorrelation_promoted_packet_extends_randomized_residual_promoted_regression :
    currentPNPApproximateDecorrelationPromotedPacket.Extends
      currentPNPRandomizedResidualPromotedPacket := by
  exact
    currentPNPApproximateDecorrelationPromotedPacket_extends_randomizedResidualPromoted

theorem current_pnp_approximate_decorrelation_promoted_packet_residual_side_information_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_randomized_residual_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_approximate_decorrelation_covered_regression :
    currentPNPApproximateDecorrelationPromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_covered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_kpoly_bridge_uncovered_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_uncovered_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_not_stop_grade_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.StopGrade := by
  exact not_stopGrade_currentPNPApproximateDecorrelationPromotedPacket

theorem current_pnp_approximate_decorrelation_promoted_packet_next_target_uncovered_regression :
    ¬ currentPNPApproximateDecorrelationPromotedPacket.covers
      currentPNPApproximateDecorrelationPromotedNextMarginalTarget := by
  exact currentPNPApproximateDecorrelationPromotedNextMarginalTarget_uncovered

theorem current_pnp_approximate_decorrelation_promoted_packet_next_target_mem_uncovered_regression :
    currentPNPApproximateDecorrelationPromotedNextMarginalTarget ∈
      currentPNPApproximateDecorrelationPromotedUncoveredRepairClasses := by
  exact
    currentPNPApproximateDecorrelationPromotedNextMarginalTarget_mem_uncovered

theorem current_pnp_approximate_decorrelation_promoted_packet_status_regression :
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
  exact currentPNPApproximateDecorrelationPromotedStatus

end Mettapedia.Computability.PNP.CruxSynthesisRegression
