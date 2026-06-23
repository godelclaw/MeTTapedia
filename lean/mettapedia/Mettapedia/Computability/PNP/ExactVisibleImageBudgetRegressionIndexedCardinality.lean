import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# Indexed Cardinality Regression Wrappers

Regression wrappers for exact visible predictor-image budgets.
-/

namespace Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression

open Mettapedia.Computability.PNP

universe u v w

variable {Index : Type u} {Input : Type v}
variable {View : Type w}
variable {Z : Type*} {k s clock : ℕ}

theorem indexed_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem indexed_not_finitePredictorCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.not_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem indexed_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
      target hinj hreal hN

theorem indexed_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem indexed_not_finitePredictorQuotient_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.not_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem indexed_finitePredictorCover_card_le_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem indexed_not_finitePredictorCover_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.not_finitePredictorCover_of_surjective_predict
    hN hsurj

theorem indexed_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover

theorem indexed_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover

theorem indexed_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem indexed_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep

theorem indexed_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

theorem indexed_finitePredictorQuotient_card_le_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem indexed_not_finitePredictorQuotient_of_surjective_predict_regression
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.not_finitePredictorQuotient_of_surjective_predict
    hN hsurj

theorem indexed_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot

theorem indexed_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict_regression
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact
    IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
      hN hfactor hsection hsurj

theorem indexed_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot

theorem indexed_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
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
    IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
      target hinj hreal hN hfactor hsection

end Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression
