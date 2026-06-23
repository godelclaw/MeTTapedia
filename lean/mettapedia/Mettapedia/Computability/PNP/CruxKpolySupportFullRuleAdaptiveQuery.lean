import Mettapedia.Computability.PNP.CruxKpolySupportFullRulePointQuery

/-!
# PNP `Kpoly` support/full-rule anchors: adaptive query decoders

Adaptive exact-visible query-tree decoder existence, fiber-constancy, and missed-root obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: an adaptive exact-visible query tree is decodable
from observed block-output traces whenever all points it may query are in
reachable support. -/
theorem kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_of_allQueriesReachable
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree :=
  supportFullRule_exists_adaptiveQueryDecoder_of_allQueriesReachable
    visibleOf tree hreach

/-- Route-coverage anchor: adaptive exact-visible query-tree decodability is
equivalent to constancy on observed-output fibers. -/
theorem kpolyCoverage_anchor_supportFullRule_adaptiveQueryDecoder_iff_constant_on_observedFibers
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree :=
  supportFullRule_exists_adaptiveQueryDecoder_iff_constant_on_observedFibers
    visibleOf tree

/-- Route-coverage anchor: two full rules with the same observed trace but
different adaptive-tree outputs refute every observed-trace decoder for that
tree. -/
theorem kpolyCoverage_anchor_supportFullRule_no_adaptiveQueryDecoder_of_same_output_eval_ne
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree :=
  supportFullRule_not_exists_adaptiveQueryDecoder_of_same_output_eval_ne
    visibleOf tree hsame hne

/-- Route-coverage anchor: a missed root query with distinct branch outputs
cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_rootAdaptiveQueryDecoder_of_missed_point_ne
    {Z : Type v} {Block : Type v} {α : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) :=
  supportFullRule_not_exists_rootAdaptiveQueryDecoder_of_missed_point_ne
    visibleOf u₀ hmiss hne


end Mettapedia.Computability.PNP
