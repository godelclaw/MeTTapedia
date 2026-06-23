import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverFactorTransport

/-!
# Regression checks for PNP Kpoly finite-cover factor-through transport

Regression anchors for generic factor-through transport, right-inverse transfer, and surjective-view lower bounds.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_finitePredictorCover_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough
    hfactor hcover

theorem kpoly_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

theorem kpoly_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

theorem kpoly_anchor_finitePredictorQuotient_of_factorsThrough_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough
    hfactor hquot

theorem kpoly_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hN hfactor hsection hsurj

theorem kpoly_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_factorsThrough_rightInverse_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index View : Type*} [Fintype View]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    2 ^ Fintype.card View ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hpayload

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_factorsThrough_rightInverse_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index View : Type*} [Fintype View]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (hs : 2 ^ s < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_surjective_predict_of_lt_card
      hs hfactor hsection hsurj

end Mettapedia.Computability.PNP.CruxSynthesisRegression
