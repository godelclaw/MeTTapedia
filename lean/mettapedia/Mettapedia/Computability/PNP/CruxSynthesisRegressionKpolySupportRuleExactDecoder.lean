import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleExactDecoder

/-!
# CruxSynthesisRegressionKpolySupportRuleExactDecoder

Exact decoder and observed-rule injectivity regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_support_full_rule_output_family_factors_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily := by
  exact
    kpolyCoverage_anchor_supportFullRule_outputFamily_factorsThrough_predictorFamily
      visibleOf

theorem kpoly_anchor_support_full_rule_observed_rule_injective_forces_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_observedRuleMap_injective_forces_surjective
      visibleOf hinj

theorem kpoly_anchor_support_full_rule_exact_decoder_forces_surjective_regression
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf := by
  exact
    kpolyCoverage_anchor_supportFullRule_exactDecoder_forces_surjective
      visibleOf decode hdecode

end Mettapedia.Computability.PNP.CruxSynthesisRegression
