import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionFiniteCovers
/-!
# P vs NP crux: exact-visible bridge obstructions

Exact-visible obstruction corollaries showing that product-bound-only and fielded-switching-only premises cannot imply below-surface exact-visible compression without a semantic finite-image theorem.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- If the chosen exact-visible family is already fully expressive, then a true
product-bound premise cannot imply below-surface exact-visible compression for
that family. -/
theorem not_productBoundExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge hprod)

/-- If the chosen exact-visible family is already fully expressive, then a true
fixed-field switching premise cannot imply below-surface exact-visible
compression for that family. -/
theorem not_fieldedSwitchingExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s) := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge hfield)

/-- Equivalently at the semantic-boundary layer, a true product-bound premise
cannot supply a below-cardinality finite predictor-image cover for a fully
expressive exact-visible family. -/
theorem not_productBoundSemanticFiniteImageBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G := by
  intro hbridge
  exact
    (not_exactVisible_finitePredictorCover_of_surjective_predict
      (Z := Z) (k := k) (Index := Index) (G := G) hs hsurj)
      (hbridge hprod)

/-- Equivalently at the semantic-boundary layer, a true fixed-field switching
premise cannot supply a below-cardinality finite predictor-image cover for a
fully expressive exact-visible family. -/
theorem not_fieldedSwitchingSemanticFiniteImageBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G := by
  intro hbridge
  exact
    (not_exactVisible_finitePredictorCover_of_surjective_predict
      (Z := Z) (k := k) (Index := Index) (G := G) hs hsurj)
      (hbridge hfield)

/-- A true product-bound-only bridge is impossible whenever any exact-visible
family in its scope is already fully expressive below the surface threshold. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge G hprod)

/-- A true fixed-field-switching-only bridge is impossible whenever any
exact-visible family in its scope is already fully expressive below the surface
threshold. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items := by
  intro hbridge
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := Index) (G := G) hs hsurj)
      (hbridge G hfield)

/-- Even the empty product-bound instance cannot imply a below-surface exact
visible compression theorem.  The product fact is true, but the full visible
Boolean family still needs the full truth-table budget. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  have hbound :
      2 ^ ([] : List (V13FieldedStep Ω)).length *
          finiteHistoryCount Ω
            (([] : List (FiniteEvent Ω)) ++
              v13FieldedSuccessEvents ([] : List (V13FieldedStep Ω))) ≤
        finiteHistoryCount Ω ([] : List (FiniteEvent Ω)) := by
    simp [v13FieldedSuccessEvents]
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hbound
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- Even an empty fielded switching certificate cannot imply below-surface exact
visible compression.  The certificate is true but has no information about the
predictor-family image. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
    trivial
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hfield
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- A nontrivial one-step Boolean-square product-bound certificate still cannot
force below-surface exact-visible compression without a semantic image theorem
for the predictor family. -/
theorem not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
    exact ⟨v13FieldPrefixInstantiation_unitField_empty, trivial⟩
  have hbound :
      2 ^ [v13BoolPairUnitFieldedStep].length *
          finiteHistoryCount (Bool × Bool)
            (([] : List (FiniteEvent (Bool × Bool))) ++
              v13FieldedSuccessEvents [v13BoolPairUnitFieldedStep]) ≤
        finiteHistoryCount (Bool × Bool)
          ([] : List (FiniteEvent (Bool × Bool))) :=
    v13_product_bound_of_fieldInstantiatedFrom
      ([] : List (FiniteEvent (Bool × Bool)))
      [v13BoolPairUnitFieldedStep] hfield
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hbound
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

/-- A nontrivial one-step fixed-field certificate itself also cannot force
below-surface exact-visible compression unless it is connected to a concrete
small predictor image. -/
theorem not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  have hfield :
      V13FieldSwitchingInstantiatedFrom
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
    exact ⟨v13FieldPrefixInstantiation_unitField_empty, trivial⟩
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := ExactVisibleRule Z k)
        (fullExactVisibleRuleFamily Z k) s :=
    hbridge (Index := ExactVisibleRule Z k) (fullExactVisibleRuleFamily Z k)
      hfield
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s) (Index := ExactVisibleRule Z k)
      (G := fullExactVisibleRuleFamily Z k)
      hs (fullExactVisibleRuleFamily_surjective Z k)) hsmall

end Mettapedia.Computability.PNP
