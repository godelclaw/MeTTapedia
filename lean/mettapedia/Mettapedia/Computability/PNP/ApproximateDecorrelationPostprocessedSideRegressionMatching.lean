import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideSkewThresholds

/-!
# Postprocessed-Side Matching/Threshold Regression Wrappers

Regression wrappers for the postprocessed-side approximate decorrelation layer.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem postprocessed_side_coin_matching_obligation_source_lower_bounds_regression
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
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox

theorem postprocessed_side_no_coin_matching_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hno

theorem postprocessed_side_coin_matching_preserves_observed_fiber_counts_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
    r side post e hpres

theorem postprocessed_side_observed_fiber_count_mismatch_blocks_coin_matching_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
      r side post z hne

theorem postprocessed_side_observed_fiber_count_mismatch_blocks_source_lower_bounds_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
      C E r side post z htrue hfalse hlt hne

theorem postprocessed_side_pointwise_collision_skew_true_count_true_regression :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding true c = true) = 2 := by
  exact postprocessedSidePointwiseCollisionSkew_true_count_true

theorem postprocessed_side_pointwise_collision_skew_false_count_true_regression :
    finiteEventCount (Fin 3)
        (fun c => postprocessedSidePointwiseCollisionSkewRecoding false c = true) = 1 := by
  exact postprocessedSidePointwiseCollisionSkew_false_count_true

theorem postprocessed_side_pointwise_collision_skew_not_count_independent_lt_three_regression
    {τ : Nat} (htol : τ < 3) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_not_countIndependentWithinToleranceOutput_of_lt_three
      htol

theorem postprocessed_side_pointwise_collision_skew_true_forward_gap_eq_three_regression :
    countIndependentWithinForwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = true) = 3 := by
  exact postprocessedSidePointwiseCollisionSkew_true_forward_gap_eq_three

theorem postprocessed_side_pointwise_collision_skew_false_backward_gap_eq_three_regression :
    countIndependentWithinBackwardGap (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2 = false) = 3 := by
  exact postprocessedSidePointwiseCollisionSkew_false_backward_gap_eq_three

theorem postprocessed_side_pointwise_collision_skew_count_independent_three_le_regression
    {τ : Nat} (hτ : 3 ≤ τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_of_three_le
      hτ

theorem postprocessed_side_pointwise_collision_skew_count_independent_iff_three_le_regression
    {τ : Nat} :
    CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
      (fun _xr => True)
      (fun xr => xr.1 = true)
      (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ ↔
      3 ≤ τ := by
  exact
    postprocessedSidePointwiseCollisionSkew_countIndependentWithinToleranceOutput_iff_three_le

theorem postprocessed_side_pointwise_collision_skew_counterexample_of_two_regression :
    ((∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse)) ∧
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true c =
            postprocessedSidePointwiseCollisionSkewRecoding false (f c)) ∧
      ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
        (fun _xr => True)
        (fun xr => xr.1 = true)
        (fun xr => postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) 2 := by
  exact
    postprocessedSidePointwiseCollisionSkew_collision_and_oneSidedMap_counterexample_of_lt_three
      (by decide)

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
