import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# PNP `Kpoly` coverage anchors: exact-visible bridge barriers

Product-bound and fixed-field-switching exact-visible bridge equivalences and obstruction anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a global product-bound-only bridge is exactly a
demand for finite predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G :=
  productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: a global fixed-field-switching-only bridge is
exactly a demand for finite predictor-image covers for every exact-visible
family. -/
theorem kpolyCoverage_anchor_fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G :=
  fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: an empty product-bound-only bridge is refuted below
the exact-visible surface threshold by the full exact-visible Boolean family. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: an empty fixed-field-switching-only bridge is
refuted below the exact-visible surface threshold by the full exact-visible
Boolean family. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        Ω Z k s ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: a nonempty Boolean-square product-bound bridge is
also refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: a nonempty Boolean-square fixed-field switching
bridge is also refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge
        (Bool × Bool) Z k s
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) hs

/-- Route-coverage anchor: any true product-bound-only bridge is refuted by an
already-surjective exact-visible family below the surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items :=
  not_productBoundOnlyExactVisibleCompressionBridge_of_true_productBound_of_surjective_predict_of_lt_surfaceCard
    G hprod hsurj hs

/-- Route-coverage anchor: any true fixed-field-switching-only bridge is
refuted by an already-surjective exact-visible family below the surface
threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items :=
  not_fieldedSwitchingOnlyExactVisibleCompressionBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_surfaceCard
    G hfield hsurj hs


end Mettapedia.Computability.PNP
