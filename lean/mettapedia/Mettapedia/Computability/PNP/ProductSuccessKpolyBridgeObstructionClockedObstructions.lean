import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionExactObstructions
/-!
# P vs NP crux: clocked-payload bridge obstructions

Clocked finite-learning payload obstruction corollaries, reduced back to the exact-visible bridge obstruction layer where appropriate.
-/

namespace Mettapedia.Computability.PNP

universe u v

/-- A true product-bound premise cannot imply the bundled clocked payload for a
fully expressive exact-visible family below the full Boolean predictor-space
cardinality. -/
theorem not_productBoundClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldedProductBoundFrom Ω hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge hprod)

/-- A true fixed-field switching premise cannot imply the bundled clocked
payload for a fully expressive exact-visible family below the full Boolean
predictor-space cardinality. -/
theorem not_fieldedSwitchingClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} {G : ExactVisibleSwitchedFamily Z k Index}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (V13FieldSwitchingInstantiatedFrom hist items →
        ClockedKpolyFiniteLearningPayload G s clock) := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge hfield)

/-- A global product-bound-only bridge to the clocked payload is impossible
whenever any exact-visible family in its scope is fully expressive below the
Boolean predictor-space threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hprod : V13FieldedProductBoundFrom Ω hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge G hprod)

/-- A global fielded-switching-only bridge to the clocked payload is impossible
whenever any exact-visible family in its scope is fully expressive below the
Boolean predictor-space threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective G.predict)
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock hist items := by
  intro hbridge
  exact
    (not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
      (Z := Z) (k := k) (s := s) (clock := clock) (Index := Index)
      (G := G) hs hsurj)
      (hbridge G hfield)

/-- The empty product-bound instance also cannot imply the clocked payload
below the exact-visible surface threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  exact
    (not_productBoundOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs)
      (productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The empty fielded-switching instance also cannot imply the clocked payload
below the exact-visible surface threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
    {Ω : Type u} [Fintype Ω] {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        Ω Z k s clock
        ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω)) := by
  intro hbridge
  exact
    (not_fieldedSwitchingOnlyExactVisibleCompressionBridge_nil_of_lt_surfaceCard
      (Ω := Ω) (Z := Z) (k := k) (s := s) hs)
      (fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The nontrivial Boolean-square one-step product-bound instance cannot imply
the clocked payload below the exact-visible surface threshold. -/
theorem not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  exact
    (not_productBoundOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)
      (productBoundOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Bool × Bool) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

/-- The nontrivial Boolean-square one-step fielded-switching instance cannot
imply the clocked payload below the exact-visible surface threshold. -/
theorem not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
        (Bool × Bool) Z k s clock
        ([] : List (FiniteEvent (Bool × Bool)))
        [v13BoolPairUnitFieldedStep] := by
  intro hbridge
  exact
    (not_fieldedSwitchingOnlyExactVisibleCompressionBridge_boolPair_one_step_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)
      (fieldedSwitchingOnlyExactVisibleCompressionBridge_of_clockedKpolyFiniteLearningBridge
        (Ω := Bool × Bool) (Z := Z) (k := k) (s := s) (clock := clock)
        hbridge)

end Mettapedia.Computability.PNP
