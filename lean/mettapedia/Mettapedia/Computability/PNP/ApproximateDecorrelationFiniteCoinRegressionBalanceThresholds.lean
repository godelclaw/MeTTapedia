import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinBalancedEvidence
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinQuantization

/-!
# Finite-coin balance-threshold regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_source_lower_bounds_lt_coin_product_forces_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r htrue hfalse happrox hlt

theorem finite_coin_recoding_source_lower_bounds_lt_coin_product_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r htrue hfalse hlt

theorem finite_coin_recoding_lt_source_coin_product_forces_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_sourceCoinProduct
      C E r happrox hlt

theorem finite_coin_recoding_lt_source_coin_product_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (τ : Nat)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_lt_sourceCoinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r hlt

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
