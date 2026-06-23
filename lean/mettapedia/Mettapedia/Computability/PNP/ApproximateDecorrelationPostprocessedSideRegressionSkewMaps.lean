import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCoinEquiv

/-!
# Postprocessed-Side Skew-Map Regression Wrappers

Regression wrappers for the postprocessed-side approximate decorrelation layer.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem postprocessed_side_pointwise_collision_skew_pointwise_regression :
    (∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) := by
  exact postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions

theorem postprocessed_side_pointwise_collision_skew_no_matching_regression :
    ¬ ∃ e : Fin 3 ≃ Fin 3,
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (e c) := by
  exact postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving

theorem postprocessed_side_pointwise_collisions_not_enough_for_matching_regression :
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
  exact postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving

theorem postprocessed_side_injective_coin_map_promotes_to_matching_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hinj : Function.Injective f) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
      r side post f hpres hinj

theorem postprocessed_side_no_matching_forces_one_sided_map_noninjective_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      r side post f hpres hno

theorem postprocessed_side_injective_coin_map_iff_matching_regression
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
      r side post

theorem postprocessed_side_injective_coin_map_iff_observed_fiber_count_eq_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
      r side post

theorem postprocessed_side_observed_fiber_mismatch_forces_one_sided_map_noninjective_regression
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_observedFiber_count_ne
      r side post f hpres z hne

theorem postprocessed_side_pointwise_collision_skew_true_to_false_map_regression :
    ∀ c : Fin 3,
      postprocessedSidePointwiseCollisionSkewRecoding true c =
        postprocessedSidePointwiseCollisionSkewRecoding false
          (postprocessedSidePointwiseCollisionSkewTrueToFalseMap c) := by
  exact postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving

theorem postprocessed_side_pointwise_collision_skew_true_to_false_map_not_injective_regression :
    ¬ Function.Injective postprocessedSidePointwiseCollisionSkewTrueToFalseMap := by
  exact postprocessedSidePointwiseCollisionSkew_trueToFalseMap_not_injective

theorem postprocessed_side_pointwise_collision_skew_any_preserving_map_not_injective_regression
    (f : Fin 3 → Fin 3)
    (hpres :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (f c)) :
    ¬ Function.Injective f := by
  exact
    postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective
      f hpres

theorem postprocessed_side_one_sided_coin_map_not_enough_for_matching_regression :
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
  exact
    postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
