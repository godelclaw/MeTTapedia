import Mettapedia.Computability.PNP.CruxKpolyCoverageExactVisibleBridge
import Mettapedia.Computability.PNP.CruxKpolyCoverageClockedBridge
import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces

/-!
# PNP `Kpoly` compression-bridge coverage core

This module contains the broad theorem-backed `Kpoly` compression-bridge
coverage proposition used by the promoted packet.  It intentionally excludes
the optional canonical ZAB ERM route so live imports can avoid that extra
manuscript-facing layer.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The broad manuscript-specific `Kpoly` bridge class is covered in the
precise theorem-backed sense that product-bound-only and fielded-switching-only
bridges, whether phrased as exact-visible compression or as bundled clocked
finite-learning payload, are exactly finite predictor-image obligations; the
parallel clocked formulations do not remove that semantic burden; and the full
exact-visible counterexamples refute those bridge schemas below the relevant
surface-cardinality and predictor-cardinality thresholds. -/
def KpolyCompressionBridgeCoverage : Prop :=
  (∀ {Ω Z : Type} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
      ProductBoundOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
        ∀ {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index),
          ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G) ∧
  (∀ {Ω Z : Type} [Fintype Ω] {k s : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
      FieldedSwitchingOnlyExactVisibleCompressionBridge Ω Z k s hist items ↔
        ∀ {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index),
          FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
      ProductBoundOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
        ∀ {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index),
          ProductBoundSemanticFiniteImageBridge Ω Z k s hist items G) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)},
      FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge Ω Z k s clock hist items ↔
        ∀ {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index),
          FieldedSwitchingSemanticFiniteImageBridge Ω Z k s hist items G) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (_hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
          Ω Z k s clock
          ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    (_hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
          Ω Z k s clock
          ([] : List (FiniteEvent Ω)) ([] : List (V13FieldedStep Ω))) ∧
  (∀ {Z : Type} [Fintype Z] {k s clock : ℕ}
    (_hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
          (Bool × Bool) Z k s clock
          ([] : List (FiniteEvent (Bool × Bool)))
          [v13BoolPairUnitFieldedStep]) ∧
  (∀ {Z : Type} [Fintype Z] {k s clock : ℕ}
    (_hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
          (Bool × Bool) Z k s clock
          ([] : List (FiniteEvent (Bool × Bool)))
          [v13BoolPairUnitFieldedStep]) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index)
    (_hprod : V13FieldedProductBoundFrom Ω hist items)
    (_hsurj : Function.Surjective G.predict)
    (_hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ ProductBoundOnlyClockedKpolyFiniteLearningBridge
          Ω Z k s clock hist items) ∧
  (∀ {Ω Z : Type} [Fintype Ω] [Fintype Z] {k s clock : ℕ}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    {Index : Type} (G : ExactVisibleSwitchedFamily Z k Index)
    (_hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (_hsurj : Function.Surjective G.predict)
    (_hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)),
      ¬ FieldedSwitchingOnlyClockedKpolyFiniteLearningBridge
          Ω Z k s clock hist items) ∧
  (∀ {Z : Type} [Fintype Z] {k s clock : ℕ} {Index : Type}
    {G : ExactVisibleSwitchedFamily Z k Index},
      ClockedKpolyFiniteLearningPayload G s clock ↔
        G.FinitePredictorCover (2 ^ s)) ∧
  (∀ {Z : Type} [Fintype Z] {k s clock : ℕ} {Index : Type}
    {G : ExactVisibleSwitchedFamily Z k Index},
      ClockedKpolyFiniteLearningPayload G s clock ↔
        ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s)

@[simp] theorem kpolyCompressionBridgeCoverage :
    KpolyCompressionBridgeCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω Z _ k s hist items
    exact
      kpolyCoverage_anchor_productBoundOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
  · intro Ω Z _ k s hist items
    exact
      kpolyCoverage_anchor_fieldedSwitchingOnlyExactVisibleCompressionBridge_iff_forall_semanticFiniteImageBridge
  · intro Ω Z _ _ k s clock hist items
    exact
      kpolyCoverage_anchor_productBoundOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
  · intro Ω Z _ _ k s clock hist items
    exact
      kpolyCoverage_anchor_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_iff_forall_semanticFiniteImageBridge
  · intro Ω Z _ _ k s clock hs
    exact
      kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs
  · intro Ω Z _ _ k s clock hs
    exact
      kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_nil_of_lt_surfaceCard
        (Ω := Ω) (Z := Z) (k := k) (s := s) (clock := clock) hs
  · intro Z _ k s clock hs
    exact
      kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) (clock := clock) hs
  · intro Z _ k s clock hs
    exact
      kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_boolPair_one_step_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) (clock := clock) hs
  · intro Ω Z _ _ k s clock hist items Index G hprod hsurj hs
    exact
      kpolyCoverage_anchor_not_productBoundOnlyClockedKpolyFiniteLearningBridge_of_true_productBound_of_surjective_predict_of_lt_predictorCard
        (G := G) (clock := clock) hprod hsurj hs
  · intro Ω Z _ _ k s clock hist items Index G hfield hsurj hs
    exact
      kpolyCoverage_anchor_not_fieldedSwitchingOnlyClockedKpolyFiniteLearningBridge_of_true_fieldedSwitching_of_surjective_predict_of_lt_predictorCard
        (G := G) (clock := clock) hfield hsurj hs
  · intro Z _ k s clock Index G
    exact
      kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover
        (G := G) (s := s) (clock := clock)
  · intro Z _ k s clock Index G
    exact
      kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_exactVisibleCompressionTarget
        (G := G) (s := s) (clock := clock)

end Mettapedia.Computability.PNP
