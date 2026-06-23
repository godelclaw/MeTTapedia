import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# Bool-pair counterexample regressions for product-success/Kpoly bridges
-/

namespace Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression

open Mettapedia.Computability.PNP

theorem product_bound_only_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem fielded_switching_only_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem product_bound_only_clocked_payload_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem fielded_switching_only_clocked_payload_bridge_bool_pair_one_step_counterexample_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem product_bound_only_bridge_bool_pair_concrete_counterexample_regression :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Bool 1 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem fielded_switching_only_bridge_bool_pair_concrete_counterexample_regression :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Bool 1 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem product_bound_only_clocked_payload_bridge_bool_pair_concrete_counterexample_regression :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Bool 1 0 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) (clock := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

theorem fielded_switching_only_clocked_payload_bridge_bool_pair_concrete_counterexample_regression :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Bool 1 0 0
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  refine
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Bool) (k := 1) (s := 0) (clock := 0) ?_
  rw [card_exactVisiblePostSwitchSurface (Z := Bool) (k := 1)]
  decide

end Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression
