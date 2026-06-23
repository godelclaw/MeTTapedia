import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCollisions

/-!
# Postprocessed-Side Source/Count Regression Wrappers

Regression wrappers for the postprocessed-side approximate decorrelation layer.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_postprocessed_side_balanced_iff_observed_fiber_count_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
    r side post

theorem finite_coin_recoding_postprocessed_side_source_lower_bounds_lt_coin_product_iff_observed_fiber_count_regression
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
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
      C E r side post htrue hfalse hlt

theorem finite_coin_recoding_postprocessed_side_lt_source_coin_product_iff_observed_fiber_count_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_observedFiber_count_eq
      C E r side post hlt

theorem postprocessed_side_observed_fiber_imbalance_products_lower_bound_regression
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
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox

theorem postprocessed_side_true_minus_false_observed_fiber_source_lower_bounds_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_trueMinusFalse_sourceLowerBounds_gt
      C E r side post z τ loTrue loFalse htrue hfalse htol

theorem postprocessed_side_false_minus_true_observed_fiber_source_lower_bounds_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_falseMinusTrue_sourceLowerBounds_gt
      C E r side post z τ loTrue loFalse htrue hfalse htol

theorem postprocessed_side_output_predicate_count_eq_of_source_lower_bounds_regression
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
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox

theorem postprocessed_side_output_predicate_true_advantage_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) <
        finiteEventCount Coin (fun c => P (post (r true c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt hgt

theorem postprocessed_side_output_predicate_false_advantage_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) <
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_falseCount_gt_trueCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt hgt

theorem postprocessed_side_output_predicate_separates_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (htruePred : ∀ c : Coin, P (post (r true c, side c)))
    (hfalsePred : ∀ c : Coin, ¬ P (post (r false c, side c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt htruePred hfalsePred

theorem postprocessed_side_output_decoder_correct_count_eq_card_of_source_lower_bounds_regression
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
    postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt happrox

theorem postprocessed_side_output_decoder_better_than_half_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      Fintype.card Coin <
        finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
          finiteEventCount Coin
            (fun c => decode (post (r false c, side c)) = false)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_gt_card_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt hgt

theorem postprocessed_side_output_decoder_recovers_blocks_source_lower_bounds_regression
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
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt hdecodeTrue hdecodeFalse

theorem postprocessed_side_source_ranges_separated_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hsep

theorem postprocessed_side_true_false_collision_obligation_source_lower_bounds_regression
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
    exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

theorem postprocessed_side_pointwise_collision_obligation_source_lower_bounds_regression
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
    postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
