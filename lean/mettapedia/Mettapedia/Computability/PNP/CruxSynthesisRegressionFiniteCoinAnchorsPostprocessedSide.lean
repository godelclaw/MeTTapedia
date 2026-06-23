import Mettapedia.Computability.PNP.CruxFiniteCoinPostprocessingAnchorsPostprocessedSide

/-!
# Regression checks for PNP postprocessed retained-side anchors

Retained-side postprocessing regression wrappers for observed fiber balance, collision, and decoder blockers.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem finite_coin_anchor_postprocessed_side_tolerance_observed_fiber_balance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideToleranceObservedFiberBalance
      C E r side post htrue hfalse hlt

theorem finite_coin_anchor_postprocessed_side_observed_fiber_imbalance_lower_bound_regression
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
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideObservedFiberImbalanceLowerBound
      C E r side post τ loTrue loFalse htrue hfalse happrox

theorem finite_coin_anchor_postprocessed_side_predicate_erasure_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePredicateErasure
      C E r side post P htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_decoder_half_accuracy_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideDecoderHalfAccuracy
      C E r side post decode htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_source_recovery_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideSourceRecoveryBlock
      C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

theorem finite_coin_anchor_postprocessed_side_collision_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCollisionObligation
      C E r side post htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_pointwise_collision_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
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
            post (r false cFalse, side cFalse)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionObligation
      C E r side post htrue hfalse hlt happrox

end Mettapedia.Computability.PNP.CruxSynthesisRegression
