import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverProbePullback

/-!
# Regression checks for PNP Kpoly finite-cover injective factor-through pullbacks

Regression anchors for injectively realized probes transported through factor maps with right inverses.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover

theorem kpoly_anchor_clocked_finite_learning_payload_card_le_of_factorsThrough_rightInverse_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ}
    {Index View : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hpayload : ClockedKpolyFiniteLearningPayload G s clock) :
    Fintype.card Probe ≤ 2 ^ s := by
  exact
    kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hpayload

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_factorsThrough_rightInverse_injective_realization_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ}
    {Index View : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : IndexedPredictorFamily Index View}
    {view : ExactVisiblePostSwitchSurface Z k → View}
    {sec : View → ExactVisiblePostSwitchSurface Z k}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hs hfactor hsection

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorCover N := by
  exact
    kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem kpoly_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem kpoly_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe Index Input View : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

end Mettapedia.Computability.PNP.CruxSynthesisRegression
