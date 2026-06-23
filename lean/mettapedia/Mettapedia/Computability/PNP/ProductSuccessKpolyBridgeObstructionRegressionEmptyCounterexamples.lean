import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# Empty-context counterexample regressions for product-success/Kpoly bridges
-/

namespace Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression

open Mettapedia.Computability.PNP

theorem product_bound_only_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem fielded_switching_only_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem product_bound_only_clocked_payload_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

theorem fielded_switching_only_clocked_payload_bridge_empty_counterexample_regression
    {Ω : Type*} [Fintype Ω] {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression
