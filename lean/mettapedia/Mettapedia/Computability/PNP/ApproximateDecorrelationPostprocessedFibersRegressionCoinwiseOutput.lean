import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersTrue
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersFalse
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceBounds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceStrict
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersZeroTolerance

/-!
# Coinwise output-fiber regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coinwise_true_fiber_output_approx_forces_product_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_false_fiber_output_approx_forces_product_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox

theorem coinwise_true_fiber_output_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_false_fiber_output_lower_bounds_force_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox

theorem coinwise_true_fiber_output_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y τ htrue hfalse htol

theorem coinwise_false_fiber_output_product_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y τ htrue hfalse htol

theorem coinwise_true_fiber_output_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_lowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

theorem coinwise_false_fiber_output_lower_bounds_block_smaller_tolerance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_lowerBounds_mul_gt
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
