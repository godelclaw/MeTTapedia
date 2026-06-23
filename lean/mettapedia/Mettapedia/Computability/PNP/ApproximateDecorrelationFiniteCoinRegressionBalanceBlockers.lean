import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinBalancedEvidence
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinQuantization

/-!
# Finite-coin balance blocker regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coin_true_fiber_count_self_positive_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    0 < coinTrueFiberCount r (r true c₀) := by
  exact coinTrueFiberCount_self_pos r c₀

theorem balanced_finite_coin_recoding_blocks_output_predicate_at_coin_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) (c₀ : Coin)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r P c₀ htrue hfalse

theorem balanced_finite_coin_recoding_blocks_nonempty_output_predicate_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates
      r P htrue hfalse

theorem balanced_finite_coin_recoding_output_predicate_counts_match_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => P (r true c)) =
      finiteEventCount Coin (fun c => P (r false c)) := by
  exact finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal

theorem balanced_finite_coin_recoding_blocks_true_count_advantage_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_trueCount_gt_falseCount
      r P hgt

theorem balanced_finite_coin_recoding_blocks_false_count_advantage_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_falseCount_gt_trueCount
      r P hgt

theorem balanced_finite_coin_recoding_decoder_correct_count_half_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => decode (r true c) = true) +
      finiteEventCount Coin (fun c => decode (r false c) = false) =
        Fintype.card Coin := by
  exact finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
    r decode hbal

theorem balanced_finite_coin_recoding_blocks_decoder_better_than_half_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin <
      finiteEventCount Coin (fun c => decode (r true c) = true) +
        finiteEventCount Coin (fun c => decode (r false c) = false)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_correctCount_gt_card
      r decode hgt

theorem balanced_finite_coin_recoding_blocks_output_decoder_at_coin_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool) (c₀ : Coin)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
      r decode c₀ htrue hfalse

theorem balanced_finite_coin_recoding_blocks_nonempty_output_decoder_regression
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers
      r decode htrue hfalse

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
