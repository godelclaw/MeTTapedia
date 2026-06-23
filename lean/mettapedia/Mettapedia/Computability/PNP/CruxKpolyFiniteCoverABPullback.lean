import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverFactorTransport
import Mettapedia.Computability.PNP.ABVisibleCompressionObstruction

/-!
# PNP `Kpoly` reduced `(a,b)` pullback anchors

This module isolates the reduced `(a,b)` view obstructions and finite-probe
pullback lower bounds for exact-visible families that factor through
`abVisibleData`.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: finite predictor-image covers cannot rescue an
exact family that factors through `(a,b)` when the reduced family is still
fully expressive and the cover is below the reduced Boolean classifier-space
cardinality. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N :=
  not_finitePredictorCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: finite predictor-image covers of an exact family
factoring through `(a,b)` inherit every injective finite-probe lower bound
already present on the reduced `(a,b)` view. -/
theorem kpolyCoverage_anchor_abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hcover

/-- Route-coverage anchor: exact visible compression is impossible below any
injective finite-probe family already realized by the reduced `(a,b)` view. -/
theorem kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  not_exactVisibleCompressionTarget_of_factorsThrough_ab_and_injective_realization_of_lt_card
    target hinj hreal hs hfactor

/-- Route-coverage anchor: representative-index covers have the same reduced
`(a,b)` pullback obstruction. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  not_finiteIndexRepresentativeCover_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: representative-index covers have the same reduced
`(a,b)` finite-probe pullback obstruction. -/
theorem kpolyCoverage_anchor_abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  abVisible_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hrep

/-- Route-coverage anchor: quotient-code presentations have the same reduced
`(a,b)` pullback obstruction. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    {Z : Type*} [Inhabited Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N :=
  not_finitePredictorQuotient_of_factorsThrough_ab_and_surjective_predict
    hN hfactor hsurj

/-- Route-coverage anchor: quotient-code presentations have the same reduced
`(a,b)` finite-probe pullback obstruction. -/
theorem kpolyCoverage_anchor_abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index} {N : ℕ}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  abVisible_finitePredictorQuotient_card_le_of_factorsThrough_of_injective_realization
    target hinj hreal hfactor hquot

/-- Route-coverage anchor: clocked exact-visible realization is impossible
below any injective finite-probe family already realized by the reduced
`(a,b)` view. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
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
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_factorsThrough_ab_and_injective_realization_of_lt_card
    target hinj hreal hs hfactor
end Mettapedia.Computability.PNP
