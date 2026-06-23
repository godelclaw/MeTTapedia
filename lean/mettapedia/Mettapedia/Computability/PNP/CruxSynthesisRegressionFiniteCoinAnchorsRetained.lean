import Mettapedia.Computability.PNP.CruxFiniteCoinPostprocessingAnchorsRetained

/-!
# Regression checks for PNP retained coin and side anchors

Retained-surface regression wrappers for exact matching, zero-tolerance, and retained-side collapse anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem finite_coin_anchor_postprocessed_side_approx_independence_coin_matching_equivalence_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideApproxIndependenceCoinMatchingEquivalence
      C E r side post htrue hfalse hlt

theorem finite_coin_anchor_coinwise_true_fiber_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    finiteCoinCoverage_anchor_coinwiseTrueFiber_sourceNonconstant_zeroBlock
      C E r y htrue hfalse hpos hneg

theorem finite_coin_anchor_coinwise_false_fiber_source_nonconstant_zero_block_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    finiteCoinCoverage_anchor_coinwiseFalseFiber_sourceNonconstant_zeroBlock
      C E r y htrue hfalse hpos hneg

theorem finite_coin_anchor_source_nonconstant_zero_iff_balanced_regression
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
    finiteCoinCoverage_anchor_sourceNonconstantZeroIffBalanced
      C E r hpos hneg

theorem finite_coin_anchor_source_lower_bound_tolerance_quantization_regression
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
    finiteCoinCoverage_anchor_sourceLowerBoundToleranceQuantization
      C E r htrue hfalse hlt

theorem finite_coin_anchor_retained_coin_tolerance_pointwise_collapse_regression
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
    finiteCoinCoverage_anchor_retainedCoinTolerancePointwiseCollapse
      C E r htrue hfalse hlt

theorem finite_coin_anchor_retained_side_tolerance_side_fiber_balance_regression
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
    finiteCoinCoverage_anchor_retainedSideToleranceSideFiberBalance
      C E r side htrue hfalse hlt

end Mettapedia.Computability.PNP.CruxSynthesisRegression
