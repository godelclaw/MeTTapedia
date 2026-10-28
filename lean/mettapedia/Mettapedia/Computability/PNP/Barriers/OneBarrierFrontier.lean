import Mettapedia.Computability.PNP.Barriers.AlgebrizationOnlyCandidate

/-!
# PNP one-barrier frontier

This module collects the three checked one-barrier replacement candidates and
proves that none of them clears the global PNP promotion gate.
-/

namespace Mettapedia.Computability.PNP

def currentPNPOneBarrierCandidatePromotionGates :
    List PNPBarrierPromotionGate :=
  [ currentPNPRelativizationOnlyPromotionGate
  , currentPNPNaturalProofOnlyPromotionGate
  , currentPNPAlgebrizationOnlyPromotionGate
  ]

theorem currentPNPOneBarrierCandidatePromotionGates_length :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 := by
  rfl

theorem currentPNPOneBarrierCandidatePromotionGates_all_fail_promotion :
    ∀ gate ∈ currentPNPOneBarrierCandidatePromotionGates,
      ¬ gate.ClearsAll := by
  intro gate hmem
  simp [currentPNPOneBarrierCandidatePromotionGates] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact currentPNPRelativizationOnlyPromotionGate_not_cleared
  · exact currentPNPNaturalProofOnlyPromotionGate_not_cleared
  · exact currentPNPAlgebrizationOnlyPromotionGate_not_cleared

theorem currentPNPOneBarrierCandidatePromotionGates_length_and_all_fail_promotion :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      (∀ gate ∈ currentPNPOneBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact
    ⟨currentPNPOneBarrierCandidatePromotionGates_length,
      currentPNPOneBarrierCandidatePromotionGates_all_fail_promotion⟩

theorem currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion :
    (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
      ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) := by
  exact
    ⟨⟨(currentPNPRelativizationOnlyBarrierStatus_verdicts).1,
        currentPNPRelativizationOnlyPromotionGate_not_cleared⟩,
      ⟨⟨(currentPNPNaturalProofOnlyBarrierStatus_verdicts).2.1,
          currentPNPNaturalProofOnlyPromotionGate_not_cleared⟩,
        ⟨(currentPNPAlgebrizationOnlyBarrierStatus_verdicts).2.2,
          currentPNPAlgebrizationOnlyPromotionGate_not_cleared⟩⟩⟩

end Mettapedia.Computability.PNP
