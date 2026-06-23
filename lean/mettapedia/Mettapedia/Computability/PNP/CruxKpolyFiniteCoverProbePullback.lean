import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverLowerBounds

/-!
# PNP `Kpoly` section-backed finite-probe pullback anchors

This module packages the section-backed finite-probe lower bounds and negative
forms for finite covers, representative covers, quotient-code presentations,
and clocked finite-learning payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: if an indexed family factors through a section-backed
reduced view, finite predictor-image covers inherit every injective finite-probe
lower bound already present on that reduced view. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
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
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hcover

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for finite predictor-image covers. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
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
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: representative-index covers inherit the same
section-backed finite-probe lower bound. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
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
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hrep

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for representative-index covers. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
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
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: quotient-code presentations inherit the same
section-backed finite-probe lower bound. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
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
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection hquot

/-- Route-coverage anchor: the section-backed finite-probe pullback lower bound
has the same negative form for quotient-code presentations. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
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
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    target hinj hreal hN hfactor hsection

/-- Route-coverage anchor: section-backed pullbacks preserve injective
finite-probe lower bounds for the bundled clocked finite-learning payload. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
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
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection
      ((kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover).1 hpayload)

/-- Route-coverage anchor: the same section-backed finite-probe lower bound
already refutes the bundled clocked finite-learning payload below the realized
probe cardinality. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
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
  intro hpayload
  exact
    (Nat.not_le_of_gt hs)
      (kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
        target hinj hreal hfactor hsection hpayload)
end Mettapedia.Computability.PNP
