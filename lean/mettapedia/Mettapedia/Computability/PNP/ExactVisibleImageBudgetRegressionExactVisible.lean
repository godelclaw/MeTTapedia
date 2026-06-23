import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# Exact-Visible Compression Regression Wrappers

Regression wrappers for exact visible predictor-image budgets.
-/

namespace Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression

open Mettapedia.Computability.PNP

universe u v w

variable {Index : Type u} {Input : Type v}
variable {View : Type w}
variable {Z : Type*} {k s clock : ℕ}

theorem exact_visible_compressionTarget_iff_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finitePredictorCover

theorem exact_visible_compressionTarget_iff_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

theorem exact_visible_compressionTarget_iff_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact exactVisibleCompressionTarget_iff_finitePredictorQuotient

theorem exact_visible_clockedRealization_iff_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finitePredictorCover

theorem exact_visible_clockedRealization_iff_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover

theorem exact_visible_clockedRealization_iff_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact exists_clockedExactVisibleRealization_iff_finitePredictorQuotient

theorem exact_visible_not_clockedRealization_iff_not_finitePredictorCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorCover (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finitePredictorCover

theorem exact_visible_not_clockedRealization_iff_not_finiteIndexRepresentativeCover_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover

theorem exact_visible_not_clockedRealization_iff_not_finitePredictorQuotient_regression
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  exact not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient

theorem exact_visible_finitePredictorCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

theorem exact_visible_finiteIndexRepresentativeCover_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

theorem exact_visible_finitePredictorQuotient_card_le_of_injective_realization_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact exactVisible_finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

theorem exact_visible_not_finitePredictorCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  exact not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem exact_visible_not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact
    not_exactVisible_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
      target hinj hreal hN

theorem exact_visible_not_finitePredictorQuotient_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  exact not_exactVisible_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

theorem exact_visible_not_compressionTarget_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    target hinj hreal hs

theorem exact_visible_not_clockedRealization_of_injective_realization_of_lt_card_regression
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem exact_visible_finitePredictorCover_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finitePredictorCover_card_le_of_surjective_predict
    hsurj hcover

theorem exact_visible_finiteIndexRepresentativeCover_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    hsurj hrep

theorem exact_visible_finitePredictorQuotient_card_le_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
    hsurj hquot

theorem exact_visible_not_finitePredictorCover_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hN hsurj

theorem exact_visible_not_finiteIndexRepresentativeCover_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict hN hsurj

theorem exact_visible_not_finitePredictorQuotient_of_surjective_predict_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact not_exactVisible_finitePredictorQuotient_of_surjective_predict hN hsurj

theorem exact_visible_not_compressionTarget_of_surjective_predict_of_lt_predictorCard_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact not_exactVisibleCompressionTarget_of_surjective_predict_of_lt_predictorCard
    hs hsurj

theorem exact_visible_not_clockedRealization_of_surjective_predict_of_lt_predictorCard_regression
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

end Mettapedia.Computability.PNP.ExactVisibleImageBudgetRegression
