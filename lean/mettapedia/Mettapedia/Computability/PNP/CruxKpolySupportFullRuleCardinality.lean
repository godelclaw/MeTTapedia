import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleAdaptiveQuery

/-!
# PNP `Kpoly` support/full-rule anchors: below-surface cardinality obstructions

Below-surface support-cardinality obstructions to injective observed maps, exact decoders, and observable point queries.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: below surface cardinality, the observed
reachable-support quotient cannot identify full exact-visible rules. -/
theorem kpolyCoverage_anchor_supportFullRule_no_observedRuleMap_injective_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict :=
  supportFullRule_not_observedRuleMap_injective_of_card_lt_surfaceCard visibleOf hcard

/-- Route-coverage anchor: cardinally small support yields two exact-visible
rules that are distinct as full predictors but indistinguishable on observed
block outputs. -/
theorem kpolyCoverage_anchor_supportFullRule_distinct_rules_same_output_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ :=
  supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
    visibleOf hcard

/-- Route-coverage anchor: below surface cardinality, no post-processing
decoder can recover all full exact-visible rules from observed block-output
traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_exactDecoder_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule :=
  supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
    visibleOf hcard

/-- Route-coverage anchor: below surface cardinality, at least one
exact-visible rule bit is not observable from the block-output quotient. -/
theorem kpolyCoverage_anchor_supportFullRule_exists_unobservable_eval_below_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ :=
  supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
    visibleOf hcard


end Mettapedia.Computability.PNP
