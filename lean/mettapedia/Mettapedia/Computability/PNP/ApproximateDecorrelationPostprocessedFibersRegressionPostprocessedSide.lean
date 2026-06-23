import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersTrue
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersFalse
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceBounds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceStrict
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersZeroTolerance

/-!
# Postprocessed side-fiber regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coin_false_fiber_count_postprocessed_side_true_fiber_empty_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    coinFalseFiberCount (fun b c => post (r b c, side c))
        (post (r true c₀, side c₀)) = 0 := by
  exact coinFalseFiberCount_postprocessedSide_trueFiber_eq_zero_of_forall_ne
    r side post c₀ hsep

theorem postprocessed_side_true_fiber_forward_gap_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀)) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r true c, side c) = post (r true c₀, side c₀)) := by
  exact countIndependentWithinForwardGap_postprocessedSide_trueFiber
    C E r side post c₀ hsep

theorem postprocessed_side_true_fiber_output_forces_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r true c, side c) = post (r true c₀, side c₀)) ≤ τ := by
  exact
    postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ hsep happrox

theorem postprocessed_side_true_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact
    sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_trueFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox

theorem postprocessed_side_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r true c, side c) = post (r true c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_product_gt
      C E r side post c₀ τ hsep htol

theorem postprocessed_side_true_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r false c, side c) ≠ post (r true c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r true c, side c) = post (r true c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_trueFiber_sourceLowerBounds_mul_gt
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs htol

theorem coin_true_fiber_count_postprocessed_side_false_fiber_empty_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    coinTrueFiberCount (fun b c => post (r b c, side c))
        (post (r false c₀, side c₀)) = 0 := by
  exact coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    r side post c₀ hsep

theorem postprocessed_side_false_fiber_backward_gap_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r false c, side c) = post (r false c₀, side c₀)) := by
  exact countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    C E r side post c₀ hsep

theorem postprocessed_side_false_fiber_output_forces_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r false c, side c) = post (r false c₀, side c₀)) ≤ τ := by
  exact
    postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox

theorem postprocessed_side_false_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact
    sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox

theorem postprocessed_side_false_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r false c, side c) = post (r false c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_product_gt
      C E r side post c₀ τ hsep htol

theorem postprocessed_side_false_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_sourceLowerBounds_mul_gt
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
