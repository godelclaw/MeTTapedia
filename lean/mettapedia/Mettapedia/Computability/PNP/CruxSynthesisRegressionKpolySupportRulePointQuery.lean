import Mettapedia.Computability.PNP.CruxKpolySupportFullRulePointQuery

/-!
# CruxSynthesisRegressionKpolySupportRulePointQuery

Point/query decoder reachability regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_support_full_rule_eval_decoder_iff_mem_range_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ := by
  exact
    kpolyCoverage_anchor_supportFullRule_evalDecoder_iff_mem_range
      visibleOf u₀

theorem kpoly_anchor_support_full_rule_all_eval_decoders_iff_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_all_evalDecoders_iff_surjective
      visibleOf

theorem kpoly_anchor_support_full_rule_query_decoder_iff_forall_mem_range_regression
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q := by
  exact
    kpolyCoverage_anchor_supportFullRule_queryDecoder_iff_forall_mem_range
      visibleOf queryOf

theorem kpoly_anchor_support_full_rule_no_query_decoder_of_missed_query_regression
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_queryDecoder_of_missed_query
      visibleOf queryOf q₀ hmiss

end Mettapedia.Computability.PNP.CruxSynthesisRegression
