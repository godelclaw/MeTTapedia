import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverEquivalences
import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces

/-!
# PNP `Kpoly` finite-cover factor-transport anchors

This module contains pullback/pushback transport across factor maps and the
section-backed surjective-summary lower bounds for finite covers and clocked
finite-learning payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: finite predictor-image covers pull back across an
explicit factor map. -/
theorem kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N :=
  IndexedPredictorFamily.finitePredictorCover_of_factorsThrough hfactor hcover

/-- Route-coverage anchor: when a factor map has a section, finite
predictor-image covers push back to the summary family. -/
theorem kpolyCoverage_anchor_finitePredictorCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N :=
  IndexedPredictorFamily.finitePredictorCover_of_factorsThrough_of_rightInverse
    hfactor hsection hcover

/-- Route-coverage anchor: finite representative-index covers pull back across
an explicit factor map. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough
    hfactor hrep

/-- Route-coverage anchor: when a factor map has a section, finite
representative-index covers push back to the summary family. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    hfactor hsection hrep

/-- Route-coverage anchor: finite quotient-code presentations pull back across
an explicit factor map. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough
    hfactor hquot

/-- Route-coverage anchor: when a factor map has a section, finite
quotient-code presentations push back to the summary family. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorQuotient_of_factorsThrough_of_rightInverse
    hfactor hsection hquot

/-- Route-coverage anchor: a section-backed factorization through a finite
summary inherits the full Boolean classifier-space lower bound from a
surjective summary family. -/
theorem kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: representative-index covers inherit the same
section-backed reduced-view obstruction. -/
theorem kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: quotient-code presentations inherit the same
section-backed reduced-view obstruction. -/
theorem kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
    hN hfactor hsection hsurj

/-- Route-coverage anchor: a section-backed factorization through a surjective
finite summary forces the full Boolean lower bound on predictor-image covers. -/
theorem kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  by_contra hN
  exact
    (kpolyCoverage_anchor_not_finitePredictorCover_of_factorsThrough_of_rightInverse
      (Nat.not_le.mp hN) hfactor hsection hsurj) hcover

/-- Route-coverage anchor: the same section-backed surjective-summary lower
bound holds for representative-index covers. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  by_contra hN
  exact
    (kpolyCoverage_anchor_not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
      (Nat.not_le.mp hN) hfactor hsection hsurj) hrep

/-- Route-coverage anchor: the same section-backed surjective-summary lower
bound holds for quotient-code presentations. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {Index Input View : Type*} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N := by
  by_contra hN
  exact
    (kpolyCoverage_anchor_not_finitePredictorQuotient_of_factorsThrough_of_rightInverse
      (Nat.not_le.mp hN) hfactor hsection hsurj) hquot

/-- Route-coverage anchor: a section-backed factorization through a fully
expressive finite summary forces the same full-Boolean lower bound on the
bundled clocked finite-learning payload. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
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
    kpolyCoverage_anchor_finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj
      ((kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover).1 hpayload)

/-- Route-coverage anchor: the same section-backed surjective-summary lower
bound already refutes the bundled clocked finite-learning payload below the
summary Boolean image size. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_factorsThrough_of_rightInverse_of_surjective_predict_of_lt_card
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
  intro hpayload
  exact
    (Nat.not_le_of_gt hs)
      (kpolyCoverage_anchor_clockedFiniteLearningPayload_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
        hfactor hsection hsurj hpayload)
end Mettapedia.Computability.PNP
