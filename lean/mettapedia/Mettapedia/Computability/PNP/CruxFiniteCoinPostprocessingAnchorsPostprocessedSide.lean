import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# PNP finite-coin postprocessing anchors: postprocessed retained side

Retained-side postprocessing anchors turning below-threshold independence into observed fiber balance and collision obligations.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: if a retained-side output is deterministically
postprocessed, then below one lower-bounded source/coin block approximate
output independence is equivalent to exact true/false balance in every
observed postprocessed fiber. -/
theorem finiteCoinCoverage_anchor_postprocessedSideToleranceObservedFiberBalance
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
  countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
    C E r side post htrue hfalse hlt

/-- Route-coverage anchor: after deterministic postprocessing of a retained-side
output, approximate output independence can only tolerate observed fibers whose
true/false residual imbalances fit inside the explicit source/coin budget. -/
theorem finiteCoinCoverage_anchor_postprocessedSideObservedFiberImbalanceLowerBound
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) :=
  sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
    C E r side post τ loTrue loFalse htrue hfalse happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, no
decidable predicate downstream of deterministic retained-side postprocessing can
have a source-side count advantage. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePredicateErasure
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
  postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post P htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, no
Boolean decoder downstream of deterministic retained-side postprocessing can
achieve better-than-half aggregate accuracy. -/
theorem finiteCoinCoverage_anchor_postprocessedSideDecoderHalfAccuracy
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin :=
  postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post decode htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block, a
downstream Boolean decoder cannot uniformly recover the source bit after
deterministic retained-side postprocessing. -/
theorem finiteCoinCoverage_anchor_postprocessedSideSourceRecoveryBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
    C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must create true/false observed
support overlap if approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCollisionObligation
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) :=
  exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must give every observed coin value
witnesses on both source sides if approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionObligation
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) :=
  postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

end Mettapedia.Computability.PNP
