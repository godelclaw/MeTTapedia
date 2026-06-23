import Mettapedia.Computability.PNP.CruxFiniteCoinPostprocessingAnchorsObstructions

/-!
# Regression checks for PNP finite-coin matching obstructions

Counterexample, predicate, and coin-matching regression wrappers for postprocessed retained-side obstructions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem finite_coin_anchor_postprocessed_side_pointwise_collision_insufficient_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionInsufficient

theorem finite_coin_anchor_postprocessed_side_one_sided_coin_map_insufficient_regression :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact finiteCoinCoverage_anchor_postprocessedSideOneSidedCoinMapInsufficient

theorem finite_coin_anchor_postprocessed_side_injective_witness_map_equivalence_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    ((∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) ∧
      ((∃ f : Coin → Coin,
        (∀ c : Coin,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
          Function.Injective f) ↔
        ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) := by
  exact finiteCoinCoverage_anchor_postprocessedSideInjectiveWitnessMapEquivalence
    r side post

theorem finite_coin_anchor_postprocessed_side_coin_matching_obligation_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingObligation
      C E r side post htrue hfalse hlt happrox

theorem finite_coin_anchor_postprocessed_side_coin_matching_cardinality_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingCardinalityBlock
      C E r side post z htrue hfalse hlt hne

theorem finite_coin_anchor_postprocessed_side_coin_matching_predicate_block_regression
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    finiteCoinCoverage_anchor_postprocessedSideCoinMatchingPredicateBlock
      C E r side post P htrue hfalse hlt hne

theorem finite_coin_anchor_postprocessed_side_predicate_matching_equivalence_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  exact
    finiteCoinCoverage_anchor_postprocessedSidePredicateMatchingEquivalence
      r side post

end Mettapedia.Computability.PNP.CruxSynthesisRegression
