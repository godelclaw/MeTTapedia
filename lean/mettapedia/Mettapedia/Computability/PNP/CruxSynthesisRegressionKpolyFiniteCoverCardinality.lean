import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverLowerBounds

/-!
# Regression checks for PNP Kpoly finite-cover cardinality lower bounds

Regression anchors for surjective and injectively realized finite-cover cardinality lower bounds.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_finitePredictorCover_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    hsurj hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_surjective_predict_regression
    {Index Input : Type*} [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hsurj : Function.Surjective G.predict)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_surjective_predict
      hsurj hpayload

theorem kpoly_anchor_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_injective_realization
      target hinj hreal hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe Index Input : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    Fintype.card Probe ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_injective_realization
      target hinj hreal hpayload

end Mettapedia.Computability.PNP.CruxSynthesisRegression
