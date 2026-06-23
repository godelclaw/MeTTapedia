import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleOneBlock

/-!
# CruxSynthesisRegressionKpolySupportRuleOneBlock

One-block full-rule support regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_one_block_full_rule_observed_small_not_exact_visible_cover_regression
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_observedSmall_and_not_exactVisibleCover
      u0 hs

theorem kpoly_anchor_one_block_full_rule_not_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_not_clockedPayload_of_lt_surfaceCard
      u0 hs

theorem kpoly_anchor_one_block_full_rule_no_exact_decoder_regression
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_no_exactDecoder
      u0 hcard

theorem kpoly_anchor_one_block_full_rule_exists_unobservable_eval_regression
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u := by
  exact
    kpolyCoverage_anchor_oneBlockFullRule_exists_unobservable_eval
      u0 hcard

end Mettapedia.Computability.PNP.CruxSynthesisRegression
