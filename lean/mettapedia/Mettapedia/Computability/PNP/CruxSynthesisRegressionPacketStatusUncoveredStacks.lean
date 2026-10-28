import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus
import Mettapedia.Computability.PNP.CruxFiniteCoinSubrepairLedger
import Mettapedia.Computability.PNP.CruxResidualSideInformationSubrepairLedger
import Mettapedia.Computability.PNP.CruxRandomizedResidualSubrepairLedger
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverage

/-!
# Regression checks for remaining uncovered PNP crux stacks

Finite-coin, residual-side-information, randomized-residual, approximate-
decorrelation, and Kpoly stack-boundary wrappers extracted from the historical
packet-status regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem finite_coin_stack_under_same_source_finite_count_regression :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  exact finiteCoinStack_under_sameSourceFiniteCountApproximation

theorem current_pnp_packet_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  exact approximateDecorrelation_uncovered_currentPNPLocalCruxPacket

theorem finite_coin_stack_broad_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact finiteCoinStack_does_not_cover_randomizedResidual

theorem randomized_residual_subrepair_stack_broad_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact randomizedResidualSubrepairStack_does_not_cover_randomizedResidual

theorem finite_coin_stack_broad_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact finiteCoinStack_does_not_cover_residualSideInformation

theorem residual_side_information_subrepair_stack_broad_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact residualSideInformationSubrepairStack_does_not_cover_residualSideInformation

theorem finite_coin_stack_broad_approximate_decorrelation_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .approximateDecorrelation := by
  exact finiteCoinStack_does_not_cover_approximateDecorrelation

theorem finite_coin_stack_broad_kpoly_bridge_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  exact finiteCoinStack_does_not_cover_kpolyCompressionBridge

theorem kpoly_subrepair_stack_broad_kpoly_bridge_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge := by
  exact kpolySubrepairStack_does_not_cover_kpolyCompressionBridge

theorem current_pnp_next_marginal_target_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers currentPNPNextMarginalTarget := by
  exact currentPNPNextMarginalTarget_uncovered

theorem current_pnp_missing_next_marginal_target_blocks_stop_grade_regression
    {packet : PNPCruxPacket}
    (hmiss : ¬ packet.covers currentPNPNextMarginalTarget) :
    ¬ packet.StopGrade := by
  exact not_stopGrade_of_not_covers_currentPNPNextMarginalTarget hmiss

theorem current_pnp_next_marginal_target_mem_uncovered_regression :
    currentPNPNextMarginalTarget ∈ currentPNPUncoveredRepairClasses := by
  exact currentPNPNextMarginalTarget_mem_uncovered

theorem current_pnp_next_marginal_target_mem_finite_coin_uncovered_regression :
    currentPNPNextMarginalTarget ∈ finiteCoinStackUncoveredBroadRepairClasses := by
  exact currentPNPNextMarginalTarget_mem_finiteCoin_uncovered_broad

end Mettapedia.Computability.PNP.CruxSynthesisRegression
