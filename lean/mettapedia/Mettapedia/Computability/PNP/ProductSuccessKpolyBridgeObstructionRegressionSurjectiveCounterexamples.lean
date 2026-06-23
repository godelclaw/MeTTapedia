import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# Surjective-family counterexample regressions for product-success/Kpoly bridges
-/

namespace Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression

open Mettapedia.Computability.PNP

universe u v

theorem product_bound_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact
    not_productBoundExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      hprod hsurj hs

theorem fielded_switching_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact
    not_fieldedSwitchingExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      hfield hsurj hs

theorem product_bound_semantic_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    not_productBoundSemanticFiniteImageBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      hprod hsurj hs

theorem fielded_switching_semantic_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    not_fieldedSwitchingSemanticFiniteImageBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      hfield hsurj hs

theorem product_bound_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    not_productBoundClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      hprod hsurj hs

theorem fielded_switching_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    not_fieldedSwitchingClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      hfield hsurj hs

theorem product_bound_only_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      G hprod hsurj hs

theorem fielded_switching_only_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      G hfield hsurj hs

theorem product_bound_only_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  exact
    not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
      G hprod hsurj hs

theorem fielded_switching_only_clocked_payload_bridge_surjective_family_counterexample_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  exact
    not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
      G hfield hsurj hs

end Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression
