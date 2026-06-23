import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedBalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedTrueFiber
import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedFalseFiber

/-!
# Regression wrappers for retained-side-channel balance and fiber obstructions.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_side_retained_balanced_iff_side_fiber_count_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) ↔
      ∀ (y : α) (s : Side),
        finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq r side

theorem finite_coin_recoding_side_retained_source_lower_bounds_lt_coin_product_iff_side_fiber_count_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
      C E r side htrue hfalse hlt

theorem finite_coin_recoding_side_retained_lt_source_coin_product_iff_side_fiber_count_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_lt_sourceCoinProduct_iff_sideFiber_count_eq
      C E r side hlt

theorem coin_true_fiber_count_with_side_true_fiber_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  exact coinTrueFiberCount_withSide_trueFiber r side c₀

theorem coin_false_fiber_count_with_side_true_fiber_empty_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) = 0 := by
  exact coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    r side c₀ hsep

theorem side_retained_true_fiber_forward_gap_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  exact countIndependentWithinForwardGap_sideRetained_trueFiber
    C E r side c₀ hsep

theorem side_retained_true_fiber_output_forces_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r true c = r true c₀ ∧ side c = side c₀) ≤ τ := by
  exact
    sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox

theorem side_retained_true_fiber_source_side_lower_bounds_force_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact
    sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox

theorem side_retained_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r true c = r true c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_product_gt
      C E r side c₀ τ hsep htol

theorem side_retained_true_fiber_source_side_lower_bounds_block_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_sourceSideLowerBounds_mul_gt
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside htol

theorem coin_false_fiber_count_with_side_false_fiber_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  exact coinFalseFiberCount_withSide_falseFiber r side c₀

theorem coin_true_fiber_count_with_side_false_fiber_empty_regression
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) = 0 := by
  exact coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    r side c₀ hsep

theorem side_retained_false_fiber_backward_gap_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  exact countIndependentWithinBackwardGap_sideRetained_falseFiber
    C E r side c₀ hsep

theorem side_retained_false_fiber_output_forces_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r false c = r false c₀ ∧ side c = side c₀) ≤ τ := by
  exact
    sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox

theorem side_retained_false_fiber_source_side_lower_bounds_force_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact
    sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox

theorem side_retained_false_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r false c = r false c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_product_gt
      C E r side c₀ τ hsep htol

theorem side_retained_false_fiber_source_side_lower_bounds_block_tolerance_regression
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_sourceSideLowerBounds_mul_gt
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
