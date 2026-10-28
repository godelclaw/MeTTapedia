import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# Postcomposition regression checks for finite-coin postprocessing foundations
-/

namespace Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression

open Mettapedia.Computability.PNP

theorem finite_output_map_fiber_card_bound_card_regression
    {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) :
    finiteOutputMapFiberCardBound g (Fintype.card α) := by
  exact finiteOutputMapFiberCardBound_card g

theorem predicate_neutral_postcompose_regression
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (P : β → Prop) [DecidablePred P]
    (hneutral : finiteCoinOutputPredicateNeutral r (fun y => P (g y))) :
    finiteCoinOutputPredicateNeutral (fun b c => g (r b c)) P := by
  exact finiteCoinOutputPredicateNeutral_postcompose r g P hneutral

theorem predicate_erasing_postcompose_regression
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) := by
  exact finiteCoinOutputPredicateErasing_postcompose r g herase

theorem fiber_balanced_postcompose_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinRecodingFiberBalanced_postcompose r g hbal

theorem true_fiber_count_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  exact coinTrueFiberCount_postcompose_injective r g hinj y

theorem false_fiber_count_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  exact coinFalseFiberCount_postcompose_injective r g hinj y

theorem fiber_balanced_of_postcompose_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj hbal

theorem fiber_balanced_postcompose_iff_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective r g hinj

theorem predicate_erasing_postcompose_iff_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_injective r g hinj

theorem fiber_balanced_of_postcompose_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
    r g recover hrecover hbal

theorem fiber_balanced_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

theorem predicate_erasing_postcompose_iff_observed_left_inverse_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

theorem fiber_balanced_of_postcompose_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    r g hinjObs hbal

theorem fiber_balanced_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    r g hinjObs

theorem observed_output_collision_of_postcompose_balanced_not_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact
    exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
      r g hbal hnot

theorem predicate_erasing_postcompose_iff_observed_injective_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinOutputPredicateErasing_postcompose_iff_of_observedInjective
    r g hinjObs

theorem false_heavy_collision_of_true_heavy_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yTrue : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue) :
    ∃ yFalse : α,
      g yFalse = g yTrue ∧ yFalse ≠ yTrue ∧
        coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact exists_falseHeavy_output_in_postprocessedFiber_of_trueHeavy
    r g hbal hheavy

theorem true_heavy_collision_of_false_heavy_postcompose_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {yFalse : α}
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hheavy : coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse) :
    ∃ yTrue : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue := by
  exact exists_trueHeavy_output_in_postprocessedFiber_of_falseHeavy
    r g hbal hheavy

theorem opposite_bias_collision_of_postcompose_balanced_not_balanced_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

end Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationRegression
