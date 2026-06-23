import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportCardinality


/-!
# PNP `Kpoly` support/full-rule anchors: observed support bounds

Observed block-output cover and clocked-payload obstruction anchors for support/full-rule actual-local interfaces.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: an actual-local interface can have observed
block-output behaviour bounded by a finite support while its full exact-visible
local-rule image still has no below-surface predictor cover. -/
theorem kpolyCoverage_anchor_supportFullRule_observedSmall_and_not_exactVisibleCover
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  supportFullRule_observedSmall_and_not_exactVisibleCover visibleOf hs

/-- Route-coverage anchor: finite observed actual-local support still does not
give the clocked finite-learning payload below the full exact-visible surface
threshold. -/
theorem kpolyCoverage_anchor_supportFullRule_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {Block : Type v} {k s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock :=
  supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard visibleOf hs


end Mettapedia.Computability.PNP
