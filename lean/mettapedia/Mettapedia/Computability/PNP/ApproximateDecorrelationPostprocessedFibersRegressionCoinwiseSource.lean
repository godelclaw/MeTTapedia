import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersTrue
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersFalse
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceBounds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceStrict
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersZeroTolerance

/-!
# Coinwise source-product regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coinwise_true_fiber_output_source_product_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_false_fiber_output_source_product_forces_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  exact
    sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_true_fiber_output_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_false_fiber_output_source_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  exact
    sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_true_fiber_output_source_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceLowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_false_fiber_output_source_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceLowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_true_fiber_output_source_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceProduct_gt
      C E r y τ htrue hfalse htol

theorem coinwise_false_fiber_output_source_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceProduct_gt
      C E r y τ htrue hfalse htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
