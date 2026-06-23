import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus

/-!
# Regression checks for the current PNP crux packet

Current local-packet status wrappers extracted from the historical packet-status
regression module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem pnp_packet_missing_repair_blocks_stop_grade_regression
    {packet : PNPCruxPacket} {repair : PNPRepairClass}
    (hmiss : ¬ packet.covers repair) :
    ¬ packet.StopGrade := by
  exact PNPCruxPacket.not_stopGrade_of_not_covers hmiss

theorem current_pnp_packet_theorem_backed_v13_status_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
        ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact currentPNPLocalCruxPacket_theoremBacked_v13_status

theorem current_pnp_strongest_honest_status_regression :
    currentPNPLocalCruxPacket.covers .repeatedPositiveFieldedPivot ∧
      currentPNPLocalCruxPacket.covers .forcedPositiveFieldedStep ∧
      currentPNPLocalCruxPacket.covers .fixedFieldBadCell ∧
      currentPNPLocalCruxPacket.covers .fieldRefinementOfBadCell ∧
      currentPNPLocalCruxPacket.covers .cdEvidenceNormalization ∧
      currentPNPLocalCruxPacket.covers .traceCaptureFactorization ∧
      currentPNPLocalCruxPacket.covers .atomicEvidenceBudget ∧
      currentPNPLocalCruxPacket.covers .acceiEnvelopeProduct ∧
      currentPNPLocalCruxPacket.covers .clockedFiniteUniformKernel ∧
      (∀ {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
        (samples :
          Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool),
        ClockedKpolyFiniteLearningPayload
          (bitVecZABDecisionListERMFamily
            (r := r) (k := k) (Index := Index) samples)
          (r + 2 * k + 1) clock) ∧
      (∀ {Z : Type v} [Fintype Z] {k s clock : ℕ}
        (_ : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
        ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
          ClockedKpolyFiniteLearningPayload G s clock)) ∧
      ¬ currentPNPLocalCruxPacket.covers .kpolyCompressionBridge ∧
      ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact currentPNPStrongestHonestStatus

theorem current_pnp_packet_not_stop_grade_regression :
    ¬ currentPNPLocalCruxPacket.StopGrade := by
  exact not_stopGrade_currentPNPLocalCruxPacket

theorem current_pnp_packet_residual_side_information_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .residualSideInformation := by
  exact residualSideInformation_uncovered_currentPNPLocalCruxPacket

theorem current_pnp_packet_randomized_residual_uncovered_regression :
    ¬ currentPNPLocalCruxPacket.covers .randomizedResidual := by
  exact randomizedResidual_uncovered_currentPNPLocalCruxPacket

theorem current_pnp_packet_same_source_finite_count_approximation_covered_regression :
    currentPNPLocalCruxPacket.covers .sameSourceFiniteCountApproximation := by
  exact sameSourceFiniteCountApproximation_covered_currentPNPLocalCruxPacket

end Mettapedia.Computability.PNP.CruxSynthesisRegression
