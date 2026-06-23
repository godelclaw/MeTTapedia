import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverABPullback

/-!
# Regression checks for PNP Kpoly finite-cover AB pullbacks

Regression anchors for reduced `(a,b)` view obstructions and finite-probe lower bounds.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  exact kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict_regression
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  exact kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

theorem kpoly_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hcover

theorem kpoly_anchor_not_exact_visible_compression_target_of_factorsThrough_ab_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

theorem kpoly_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hrep

theorem kpoly_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N := by
  exact
    kpolyCoverage_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
      target hinj hreal hfactor hquot

theorem kpoly_anchor_not_clocked_realization_of_factorsThrough_ab_injective_probe_regression
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
      target hinj hreal hs hfactor

end Mettapedia.Computability.PNP.CruxSynthesisRegression
