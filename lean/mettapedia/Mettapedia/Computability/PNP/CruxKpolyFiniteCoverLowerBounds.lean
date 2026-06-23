import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverABPullback

/-!
# PNP `Kpoly` generic finite-cover lower-bound anchors

This module contains the direct surjectivity and injective-realization lower
bounds for finite predictor-image covers, representative-index covers,
quotient-code presentations, and clocked finite-learning payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a fully expressive finite indexed family cannot have
a finite predictor-image cover smaller than the full Boolean classifier space. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

/-- Route-coverage anchor: representative-index covers obey the same generic
full-Boolean lower bound under surjectivity. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card Input ≤ N := by
  have hcover : G.FinitePredictorCover N :=
    (kpolyCoverage_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover).2 hrep
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict hsurj hcover

/-- Route-coverage anchor: quotient-code presentations obey the same generic
full-Boolean lower bound under surjectivity. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_surjective_predict
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N := by
  have hcover : G.FinitePredictorCover N :=
    (kpolyCoverage_anchor_finitePredictorCover_iff_finitePredictorQuotient).2 hquot
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict hsurj hcover

/-- Route-coverage anchor: a fully expressive exact-visible family forces the
bundled clocked finite-learning payload to budget at least the full Boolean
image size. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_surjective_predict
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict hsurj
      ((kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover).1 hpayload)

/-- Route-coverage anchor: finite predictor-image covers must be at least as
large as any injectively indexed finite probe family already realized by the
indexed predictors. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

/-- Route-coverage anchor: representative-index covers have the same finite
probe lower bound. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

/-- Route-coverage anchor: quotient-code presentations have the same finite
probe lower bound. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_injective_realization
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

/-- Route-coverage anchor: any injectively realized finite probe family also
forces the bundled clocked finite-learning payload to budget at least the
realized probe cardinality. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_injective_realization
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    Fintype.card Probe ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_injective_realization
      target hinj hreal
      ((kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover).1 hpayload)
end Mettapedia.Computability.PNP
