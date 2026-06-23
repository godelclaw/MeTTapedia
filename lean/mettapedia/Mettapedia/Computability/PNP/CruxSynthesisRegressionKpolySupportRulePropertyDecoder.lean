import Mettapedia.Computability.PNP.CruxKpolySupportFullRulePropertyDecoder

/-!
# CruxSynthesisRegressionKpolySupportRulePropertyDecoder

Property-decoder constancy and obstruction regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_support_full_rule_property_decoder_constant_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁) :
    property rule₀ = property rule₁ := by
  exact
    kpolyCoverage_anchor_supportFullRule_propertyDecoder_constant_on_observedFibers
      visibleOf property decode hdecode hsame

theorem kpoly_anchor_support_full_rule_property_decoder_iff_constant_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ := by
  exact
    kpolyCoverage_anchor_supportFullRule_propertyDecoder_iff_constant_on_observedFibers
      visibleOf property

theorem kpoly_anchor_support_full_rule_no_property_decoder_regression
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule := by
  exact
    kpolyCoverage_anchor_supportFullRule_no_propertyDecoder_of_same_output_ne
      visibleOf property hsame hprop

end Mettapedia.Computability.PNP.CruxSynthesisRegression
