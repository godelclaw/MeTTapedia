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
    HasTwoSourceBootstrapSlack benFavorableRecombinationConstant 2 16 ∧
      rgGain benFavorableRecombinationConstant 2 16 = (693 : ℝ) / 2560 ∧
      (∀ dmax : ℕ, dmax ≤ 15 →
        ¬ HasTwoSourceBootstrapSlack benFavorableRecombinationConstant 2 dmax) := by
  exact
    ⟨benFavorableRecombination_twoSourceSlack_two_sixteen,
      benFavorableRecombination_gain_two_sixteen_eq,
      fun dmax hdmax =>
        not_benFavorableRecombination_twoSourceSlack_two_of_dmax_le_fifteen
          hdmax⟩

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
    recombinationConstantSteelmanRow.verdict = .verified ∧
      supportRecurrenceSteelmanRow.verdict = .reducedToNamedAssumption ∧
      twoMarkedIdentitySteelmanRow.verdict = .reducedToNamedAssumption ∧
      kpWilsonSteelmanRow.verdict = .reducedToNamedAssumption ∧
      realRGRecursionSteelmanRow.verdict = .reducedToNamedAssumption ∧
      proBlueprintSteelmanRow.verdict = .blockedByUnreadableArtifact := by
  exact
    ⟨recombinationConstantSteelman_verified,
      supportRecurrenceSteelman_reduced,
      twoMarkedIdentitySteelman_reduced,
      kpWilsonSteelman_reduced,
      realRGRecursionSteelman_reduced,
      proBlueprintSteelman_blocked⟩

end YangMills
end QuantumTheory
end Mettapedia
