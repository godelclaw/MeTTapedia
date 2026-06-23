import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleObserved

/-!
# CruxSynthesisRegressionKpolySupportRuleObserved

Observed-output and non-cover support/full-rule regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_support_full_rule_observed_small_not_full_cover_regression
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    kpolyCoverage_anchor_supportFullRule_observedSmall_and_not_exactVisibleCover
      visibleOf hs

theorem kpoly_anchor_support_full_rule_not_clocked_payload_regression
    {Z : Type v} [Fintype Z] {Block : Type v} {k s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_supportFullRule_not_clockedPayload_of_lt_surfaceCard
      visibleOf hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
