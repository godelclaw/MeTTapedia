import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportOneBlock

/-!
# PNP `Kpoly` support/full-rule anchors: one-block specializations

One-block support/full-rule specializations of observed-smallness, payload, exact-decoder, and unobservable-eval obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a one-block actual-local interface is the minimal
finite-support instance of the same obstruction. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_observedSmall_and_not_exactVisibleCover
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) :=
  oneBlockFullRule_observedSmall_and_not_exactVisibleCover u0 hs

/-- Route-coverage anchor: the same one-block actual-local interface refutes
deriving the clocked finite-learning payload from observed support smallness. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_not_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock :=
  oneBlockFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard u0 hs

/-- Route-coverage anchor: the one-block support quotient admits no exact full
rule decoder once the exact-visible surface has more than one point. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_no_exactDecoder
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule :=
  oneBlockFullRule_not_exists_exactDecoder_of_one_lt_surfaceCard u0 hcard

/-- Route-coverage anchor: in the one-block case, some exact-visible rule bit
is not observable once the exact-visible surface has more than one point. -/
theorem kpolyCoverage_anchor_oneBlockFullRule_exists_unobservable_eval
    {Z : Type v} [Fintype Z] {k : ℕ}
    (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u :=
  oneBlockFullRule_exists_unobservable_eval_of_one_lt_surfaceCard u0 hcard


end Mettapedia.Computability.PNP
