import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces
import Mettapedia.Computability.PNP.CruxKpolyCoverageExactVisibleBridge

/-!
# CruxSynthesisRegressionKpolyVisibleBridgeInterfaces

Clocked/exact-visible interface and product/fielded bridge regressions.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_clocked_realization_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact
    kpolyCoverage_anchor_clockedRealization_iff_exactVisibleCompressionTarget
      (G := G) (s := s) (clock := clock)

theorem kpoly_anchor_exact_visible_compression_target_iff_finite_predictor_cover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover

theorem kpoly_anchor_product_bound_only_bridge_iff_forall_semantic_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_fielded_switching_only_bridge_iff_forall_semantic_finite_image_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  exact
    kpolyCoverage_anchor_fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

theorem kpoly_anchor_not_product_bound_only_bridge_nil_of_lt_surface_card_regression
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_nil_of_lt_surface_card_regression
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_product_bound_only_bridge_bool_pair_one_step_of_lt_surface_card_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_bool_pair_one_step_of_lt_surface_card_regression
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs

theorem kpoly_anchor_not_product_bound_only_bridge_surjective_family_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
      G hprod hsurj hs

theorem kpoly_anchor_not_fielded_switching_only_bridge_surjective_family_regression
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  exact
    kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
      G hfield hsurj hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
