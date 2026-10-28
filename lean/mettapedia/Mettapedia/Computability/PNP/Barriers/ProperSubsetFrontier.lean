import Mettapedia.Computability.PNP.Barriers.TwoBarrierFrontier

/-!
# PNP proper-subset barrier frontier

This module combines the checked one-barrier and two-barrier replacement
frontiers.  The current strict-subset candidates all fail the global PNP
promotion gate, so a future replacement route must represent all three
barrier layers before it is tested as a global route.
-/

namespace Mettapedia.Computability.PNP

def currentPNPProperSubsetBarrierCandidatePromotionGates :
    List PNPBarrierPromotionGate :=
  currentPNPOneBarrierCandidatePromotionGates ++
    currentPNPTwoBarrierCandidatePromotionGates

theorem currentPNPProperSubsetBarrierCandidatePromotionGates_mem
    {gate : PNPBarrierPromotionGate} :
    gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates ↔
      gate ∈ currentPNPOneBarrierCandidatePromotionGates ∨
        gate ∈ currentPNPTwoBarrierCandidatePromotionGates := by
  simp [currentPNPProperSubsetBarrierCandidatePromotionGates]

theorem currentPNPProperSubsetBarrierCandidatePromotionGates_length :
    currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 := by
  simp [currentPNPProperSubsetBarrierCandidatePromotionGates,
    currentPNPOneBarrierCandidatePromotionGates_length,
    currentPNPTwoBarrierCandidatePromotionGates_length]

theorem currentPNPProperSubsetBarrierCandidatePromotionGates_all_fail_promotion :
    ∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
      ¬ gate.ClearsAll := by
  intro gate hmem
  rw [currentPNPProperSubsetBarrierCandidatePromotionGates_mem] at hmem
  rcases hmem with hone | htwo
  · exact currentPNPOneBarrierCandidatePromotionGates_all_fail_promotion gate hone
  · exact currentPNPTwoBarrierCandidatePromotionGates_all_fail_promotion gate htwo

theorem currentPNPProperSubsetBarrierCandidatePromotionGates_lengths_and_failures :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      (∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) := by
  exact
    ⟨currentPNPOneBarrierCandidatePromotionGates_length,
      currentPNPTwoBarrierCandidatePromotionGates_length,
      currentPNPProperSubsetBarrierCandidatePromotionGates_length,
      currentPNPProperSubsetBarrierCandidatePromotionGates_all_fail_promotion⟩

theorem currentPNPProperSubsetBarrierFrontier_all_strict_subsets_fail_promotion :
    currentPNPOneBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPTwoBarrierCandidatePromotionGates.length = 3 ∧
      currentPNPProperSubsetBarrierCandidatePromotionGates.length = 6 ∧
      (∀ gate ∈ currentPNPProperSubsetBarrierCandidatePromotionGates,
        ¬ gate.ClearsAll) ∧
      (currentPNPRelativizationOnlyBarrierStatus.relativization = .cleared ∧
        ¬ currentPNPRelativizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofOnlyBarrierStatus.naturalProof = .cleared ∧
        ¬ currentPNPNaturalProofOnlyPromotionGate.ClearsAll) ∧
      (currentPNPAlgebrizationOnlyBarrierStatus.algebrization = .cleared ∧
        ¬ currentPNPAlgebrizationOnlyPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationNaturalProofBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationNaturalProofBarrierStatus.naturalProof =
          .cleared ∧
        ¬ currentPNPRelativizationNaturalProofPromotionGate.ClearsAll) ∧
      (currentPNPRelativizationAlgebrizationBarrierStatus.relativization =
          .cleared ∧
        currentPNPRelativizationAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPRelativizationAlgebrizationPromotionGate.ClearsAll) ∧
      (currentPNPNaturalProofAlgebrizationBarrierStatus.naturalProof =
          .cleared ∧
        currentPNPNaturalProofAlgebrizationBarrierStatus.algebrization =
          .cleared ∧
        ¬ currentPNPNaturalProofAlgebrizationPromotionGate.ClearsAll) := by
  exact
    ⟨(currentPNPProperSubsetBarrierCandidatePromotionGates_lengths_and_failures).1,
      (currentPNPProperSubsetBarrierCandidatePromotionGates_lengths_and_failures).2.1,
      (currentPNPProperSubsetBarrierCandidatePromotionGates_lengths_and_failures).2.2.1,
      (currentPNPProperSubsetBarrierCandidatePromotionGates_lengths_and_failures).2.2.2,
      (currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion).1,
      (currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion).2.1,
      (currentPNPOneBarrierFrontier_all_single_layer_clearances_fail_promotion).2.2,
      (currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion).1,
      (currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion).2.1,
      (currentPNPTwoBarrierFrontier_all_double_layer_clearances_fail_promotion).2.2⟩

end Mettapedia.Computability.PNP
