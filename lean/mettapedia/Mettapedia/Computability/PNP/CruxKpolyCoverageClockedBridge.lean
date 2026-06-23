import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionClockedObstructions

/-!
# PNP `Kpoly` coverage anchors: clocked finite-learning bridge barriers

Product-bound and fixed-field-switching clocked finite-learning bridge equivalences and obstruction anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a global product-bound-only bridge to the full
clocked finite-learning payload is still exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G :=
  productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: a global fixed-field-switching-only bridge to the
full clocked finite-learning payload is still exactly a demand for finite
predictor-image covers for every exact-visible family. -/
theorem kpolyCoverage_anchor_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)} :
    FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
      ∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G :=
  fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge

/-- Route-coverage anchor: an empty product-bound-only bridge to the full
clocked payload is refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: an empty fixed-field-switching-only bridge to the
full clocked payload is refuted below the exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: the nonempty Boolean-square product-bound bridge to
the full clocked payload is also refuted below the exact-visible surface
threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: the nonempty Boolean-square fixed-field switching
bridge to the full clocked payload is also refuted below the exact-visible
surface threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

/-- Route-coverage anchor: any true product-bound-only bridge to the full
clocked payload is refuted by an already-surjective exact-visible family below
the Boolean predictor-space threshold. -/
theorem kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items :=
  not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    G hprod hsurj hs

/-- Route-coverage anchor: any true fixed-field-switching-only bridge to the
full clocked payload is refuted by an already-surjective exact-visible family
below the Boolean predictor-space threshold. -/
theorem kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} {Z : Type v} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items :=
  not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    G hfield hsurj hs


end Mettapedia.Computability.PNP
