import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverObstructions

/-!
# Regression checks for PNP Kpoly exact-visible finite-cover obstructions

Regression anchors for exact-visible surjective and injective terminal obstructions to compression and clocked payloads.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_not_exact_visible_finitePredictorCover_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_exactVisible_finitePredictorCover_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_exact_visible_finiteIndexRepresentativeCover_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_exact_visible_finitePredictorQuotient_of_surjective_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_exactVisible_finitePredictorQuotient_of_surjective_predict
    hN hsurj

theorem kpoly_anchor_not_clocked_realization_of_surjective_predict_of_lt_predictorCard_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact kpolyCoverage_anchor_not_clockedRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_surjective_predict_of_lt_predictorCard_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      hs hsurj

theorem kpoly_anchor_not_exact_visible_compression_target_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem kpoly_anchor_not_clocked_realization_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_of_injective_realization_of_lt_card
      target hinj hreal hs

theorem kpoly_anchor_not_clocked_finite_learning_payload_of_injective_realization_of_lt_card_regression
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock := by
  exact
    kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_injective_realization_of_lt_card
      target hinj hreal hs


end Mettapedia.Computability.PNP.CruxSynthesisRegression
