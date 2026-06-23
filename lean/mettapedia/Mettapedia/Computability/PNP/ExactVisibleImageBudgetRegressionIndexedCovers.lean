import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# Indexed Cover/Quotient Regression Wrappers

Regression wrappers for exact visible predictor-image budgets.
-/

namespace Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression

open Mettapedia.Computability.PNP

universe u v w

variable {Index : Type u} {Input : Type v}
variable {View : Type w}
variable {Z : Type*} {k s clock : ℕ}

theorem indexed_hasBitBudget_iff_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover

theorem indexed_finitePredictorCover_of_hasBitBudget_regression
    {G : IndexedPredictorFamily Index Input}
    (hsmall : G.HasBitBudget s) :
    G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget hsmall

theorem indexed_hasBitBudget_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input}
    (hcover : G.FinitePredictorCover (2 ^ s)) :
    G.HasBitBudget s := by
  exact IndexedPredictorFamily.hasBitBudget_of_finitePredictorCover hcover

theorem indexed_finitePredictorCover_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  exact IndexedPredictorFamily.finitePredictorCover_mono hNM hcover

theorem indexed_finitePredictorCover_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_factorsThrough
    hfactor hcover

theorem indexed_finitePredictorCover_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

theorem indexed_finitePredictorCover_iff_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover

theorem indexed_hasBitBudget_iff_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finiteIndexRepresentativeCover

theorem indexed_hasBitBudget_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} :
    G.HasBitBudget s ↔ G.FinitePredictorQuotient (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorQuotient

theorem indexed_finitePredictorCover_of_finiteIndexRepresentativeCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_finiteIndexRepresentativeCover hrep

theorem indexed_finiteIndexRepresentativeCover_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_finitePredictorCover
    hcover

theorem indexed_finitePredictorCover_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient

theorem indexed_finiteIndexRepresentativeCover_iff_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_iff_finitePredictorQuotient

theorem indexed_finitePredictorCover_of_finitePredictorQuotient_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorCover N := by
  exact IndexedPredictorFamily.finitePredictorCover_of_finitePredictorQuotient
    hquot

theorem indexed_finitePredictorQuotient_of_finitePredictorCover_regression
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_finitePredictorCover
    hcover

theorem indexed_finiteIndexRepresentativeCover_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_mono hNM hrep

theorem indexed_finiteIndexRepresentativeCover_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

theorem indexed_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

theorem indexed_finitePredictorQuotient_mono_regression
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  exact IndexedPredictorFamily.finitePredictorQuotient_mono hNM hquot

theorem indexed_finitePredictorQuotient_of_factorsThrough_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough
    hfactor hquot

theorem indexed_finitePredictorQuotient_of_factorsThrough_of_rightInverse_regression
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N := by
  exact IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

end Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression
