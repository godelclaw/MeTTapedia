import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinBalancedEvidence
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinQuantization

/-!
# Finite-coin fiber-count regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_true_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_trueFiber C E r y

theorem finite_coin_recoding_false_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_falseFiber C E r y

theorem finite_coin_recoding_fiber_count_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  exact finiteEventCount_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_forward_gap_imbalance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  exact countIndependentWithinForwardGap_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_backward_gap_imbalance_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  exact countIndependentWithinBackwardGap_finiteCoinRecoding_fiber C E r y

theorem finite_coin_recoding_balanced_fibers_exactly_decorrelate_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
    C E r hbal


end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
