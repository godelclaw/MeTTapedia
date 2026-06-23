import Mettapedia.Computability.PNP.ApproximateDecorrelationCoinRetained

/-!
# Regression wrappers for retained-coin preservation obstructions.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_coin_retained_balanced_iff_pointwise_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) ↔
      ∀ c : Coin, r true c = r false c := by
  exact finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq r

theorem finite_coin_recoding_coin_retained_source_lower_bounds_lt_coin_product_iff_pointwise_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
      C E r htrue hfalse hlt

theorem finite_coin_recoding_coin_retained_lt_source_coin_product_iff_pointwise_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_lt_sourceCoinProduct_iff_pointwise_eq
      C E r hlt

theorem coin_true_fiber_count_with_coin_true_fiber_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 1 := by
  exact coinTrueFiberCount_withCoin_trueFiber r c₀

theorem coin_false_fiber_count_with_coin_true_fiber_empty_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    coinFalseFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 0 := by
  exact coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep

theorem coin_retained_true_fiber_forward_gap_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin := by
  exact countIndependentWithinForwardGap_coinRetained_trueFiber C E r c₀ hsep

theorem coin_retained_true_fiber_output_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox

theorem coin_retained_true_fiber_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ loTrue loFalse hsep htrue hfalse happrox

theorem coin_retained_true_fiber_source_product_blocks_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceProduct_gt
      C E r c₀ τ hsep htol

theorem coin_retained_true_fiber_source_lower_bounds_block_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse * Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceLowerBounds_mul_gt
      C E r c₀ τ loTrue loFalse hsep htrue hfalse htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
