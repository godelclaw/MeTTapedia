import Mettapedia.QuantumTheory.YangMills.CompletionSteelman

/-!
# Regression checks for the Yang-Mills five-input completion steelman
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem completionSteelman_recombination_regression :
    ¬ V14LiteralExtractionRecombinationClaims ∧
      HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 15 ∧
      (∀ D : ℕ, D ≤ 14 →
        ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D) := by
  exact
    ⟨not_v14LiteralExtractionRecombinationClaims,
      proposedMajorantLedger_twoSourceSlack_two_fifteen,
      fun _ hD =>
        not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen hD⟩

theorem completionSteelman_support_regression :
    (∀ {r : ℕ → ℝ} {A : ℝ}, 0 ≤ A →
      (∀ j, r (j + 1) ≤ r j / 2 + A) →
        ∀ J, r J ≤ r 0 / 2 ^ J + 2 * A) ∧
    (∀ {r0 A : ℝ}, 0 < A → ∀ M : ℝ,
      ∃ J : ℕ, M < badSupportEnvelope r0 A J) := by
  exact
    ⟨fun hA hrec => benGlueSupport_safeBranch_uniform hA hrec,
      fun hA M => benGlueSupport_badBranch_unbounded hA M⟩

theorem completionSteelman_twoMarked_canary_regression :
    (∀ A : Unit,
      oneMarkedCanaryExpectation0 A =
        oneMarkedCanaryExpectationJ (oneMarkedCanaryQ A)) ∧
    ¬ (∀ A B : Unit,
      oneMarkedCanaryCorr0 A (oneMarkedCanaryTau0 B) =
        oneMarkedCanaryCorrJ (oneMarkedCanaryQ A)
          (oneMarkedCanaryTauJ (oneMarkedCanaryQ B))) := by
  exact
    ⟨oneMarkedCanary_pushforward,
      oneMarkedPushforward_does_not_imply_twoMarked_canary⟩

theorem completionSteelman_primary_verdicts_regression :
    recombinationConstantSteelmanRow.verdict = .refutedOrInconsistent ∧
      supportRecurrenceSteelmanRow.verdict = .reducedToNamedAssumption ∧
      twoMarkedIdentitySteelmanRow.verdict = .reducedToNamedAssumption ∧
      kpWilsonSteelmanRow.verdict = .reducedToNamedAssumption ∧
      realRGRecursionSteelmanRow.verdict = .reducedToNamedAssumption ∧
      proBlueprintSteelmanRow.verdict = .verified := by
  exact
    ⟨recombinationConstantSteelman_refutedOrInconsistent,
      supportRecurrenceSteelman_reduced,
      twoMarkedIdentitySteelman_reduced,
      kpWilsonSteelman_reduced,
      realRGRecursionSteelman_reduced,
      proBlueprintSteelman_verified⟩

#print axioms wilsonPlaquetteHolonomy_gaugeAct
#print axioms specialUnitaryWilsonPotential
#print axioms FiniteWilsonBlock.polynomialEvaluate_gaugeInvariant
#print axioms FiniteWilsonBlock.polynomialMajorantNorm_truncate_le
#print axioms projectionRangeSpecification_does_not_imply_bound_two
#print axioms coefficientL1_basisJetProjection_le
#print axioms polymerActivityMajorant_recombineByUnion_le
#print axioms fourteen_lt_contactStrip_rail_contacts
#print axioms rootedTwoPolymerConnectionChoices_card
#print axioms exp_half_lt_exp_fluctuationBigOExponent_two_two
#print axioms three_b_four_lt_sixVertexTreeCode_card
#print axioms not_v14LiteralExtractionRecombinationClaims
#print axioms proposedMajorantLedger_leastDepth_and_leastEvenDepth

end YangMills
end QuantumTheory
end Mettapedia
