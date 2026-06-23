import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinBalancedEvidence
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinQuantization

/-!
# Finite-coin zero-tolerance nonconstant regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem finite_coin_recoding_true_minus_false_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinFalseFiberCount r y < coinTrueFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
      C E r y hpos hneg himb

theorem finite_coin_recoding_false_minus_true_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinTrueFiberCount r y < coinFalseFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
      C E r y hpos hneg himb

theorem finite_coin_recoding_source_nonconstant_zero_iff_balanced_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
      C E r hpos hneg

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
