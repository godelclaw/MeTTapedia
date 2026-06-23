import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleExactDecoder

/-!
# PNP `Kpoly` support/full-rule anchors: property decoders

Property-decoder fiber-constancy equivalences and obstruction anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: any downstream property decoded from observed
block-output traces must be constant on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_propertyDecoder_constant_on_observedFibers
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
    property rule₀ = property rule₁ :=
  supportFullRule_propertyDecoder_constant_on_observedFibers
    visibleOf property decode hdecode hsame

/-- Route-coverage anchor: a downstream property is decodable from observed
block-output traces exactly when it is constant on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_propertyDecoder_iff_constant_on_observedFibers
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
        property rule₀ = property rule₁ :=
  supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
    visibleOf property

/-- Route-coverage anchor: any downstream property separating one observed
fiber cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_propertyDecoder_of_same_output_ne
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
          property rule :=
  supportFullRule_not_exists_propertyDecoder_of_same_output_ne
    visibleOf property hsame hprop


end Mettapedia.Computability.PNP
