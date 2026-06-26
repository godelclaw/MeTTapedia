import Mettapedia.Computability.PNP.CruxKpolyPromotedPacket

/-!
# Regression checks for the Kpoly-compression promoted PNP crux packet

Kpoly-compression-bridge promoted-packet status wrappers extracted from the
historical packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_kpoly_compression_bridge_promoted_packet_extends_approximate_decorrelation_promoted_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.Extends
      currentPNPApproximateDecorrelationPromotedPacket := by
  exact
    currentPNPKpolyCompressionBridgePromotedPacket_extends_approximateDecorrelationPromoted

theorem current_pnp_kpoly_compression_bridge_promoted_packet_residual_side_information_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .residualSideInformation := by
  exact
    residualSideInformation_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_randomized_residual_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .randomizedResidual := by
  exact randomizedResidual_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_approximate_decorrelation_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .approximateDecorrelation := by
  exact
    approximateDecorrelation_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_kpoly_bridge_covered_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.covers
      .kpolyCompressionBridge := by
  exact
    kpolyCompressionBridge_covered_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_refutation_packet_regression :
    (∀ {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
      {G : ExactVisibleSwitchedFamily Z k Index},
        ClockedKpolyFiniteLearningPayload G s clock ↔
          G.FinitePredictorCover (2 ^ s)) ∧
      (∀ {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ},
        s < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
              Ω Z k s clock
              ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) ∧
      (∀ {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ},
        s < Fintype.card (ExactVisiblePostSwitchSurface Z k) →
          ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
              Ω Z k s clock
              ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) := by
  exact currentPNPKpolyCompressionBridgeCoverage_refutation_packet

theorem current_pnp_kpoly_compression_bridge_promoted_packet_covers_current_gaps_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.CoversList
      currentPNPUncoveredRepairClasses := by
  exact currentPNPKpolyCompressionBridgePromotedPacket_covers_current_gaps

theorem current_pnp_kpoly_compression_bridge_promoted_packet_stop_grade_regression :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade := by
  exact stopGrade_currentPNPKpolyCompressionBridgePromotedPacket

theorem current_pnp_kpoly_compression_bridge_promoted_packet_status_regression :
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
  exact currentPNPKpolyCompressionBridgePromotedStatus

end Mettapedia.Computability.PNP.CruxSynthesisRegression
