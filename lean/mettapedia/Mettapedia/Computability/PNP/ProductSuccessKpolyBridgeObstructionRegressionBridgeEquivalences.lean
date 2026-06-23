import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# Product-success/Kpoly bridge equivalence regressions
-/

namespace Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression

open Mettapedia.Computability.PNP

universe u v

theorem full_exact_visible_rule_family_surjective_regression
    (Z : Type*) (k : ℕ) :
    Function.Surjective (fullExactVisibleRuleFamily Z k).predict := by
  exact fullExactVisibleRuleFamily_surjective Z k

theorem product_bound_semantic_bridge_iff_exact_visible_compression_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact productBoundSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge

theorem product_bound_true_bridge_iff_finite_predictor_cover_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact productBound_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    hprod

theorem product_bound_only_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem fielded_switching_semantic_bridge_iff_exact_visible_compression_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index} :
    FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G ↔
      (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  exact fieldedSwitchingSemanticFiniteImageBridge_iff_exactVisibleCompressionBridge

theorem fielded_switching_true_bridge_iff_finite_predictor_cover_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact fieldedSwitching_true_exactVisibleCompressionBridge_iff_finitePredictorCover
    hfield

theorem fielded_switching_only_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem product_bound_only_clocked_payload_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem fielded_switching_only_clocked_payload_bridge_iff_forall_semantic_finite_image_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

theorem product_bound_clocked_payload_bridge_implies_exact_visible_compression_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
      hbridge

theorem fielded_switching_clocked_payload_bridge_implies_exact_visible_compression_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hbridge :
      FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items) :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
      hbridge

theorem finite_predictor_cover_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorCover (2 ^ s) := by
  exact finitePredictorCover_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_representative_cover_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact finiteIndexRepresentativeCover_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_quotient_of_product_bound_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hprod : V13FieldedProductBoundFrom Ω hist items) :
    G.FinitePredictorQuotient (2 ^ s) := by
  exact finitePredictorQuotient_of_productBoundOnlyExactVisibleCompressionBridge
    G hbridge hprod

theorem finite_predictor_cover_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorCover (2 ^ s) := by
  exact finitePredictorCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

theorem finite_representative_cover_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact finiteIndexRepresentativeCover_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

theorem finite_quotient_of_fielded_switching_only_bridge_regression
    {Ω : Type u} [Fintype Ω] {Z : Type v} {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hbridge : FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items) :
    G.FinitePredictorQuotient (2 ^ s) := by
  exact finitePredictorQuotient_of_fieldedSwitchingOnlyExactVisibleCompressionBridge
    G hbridge hfield

end Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionRegression
