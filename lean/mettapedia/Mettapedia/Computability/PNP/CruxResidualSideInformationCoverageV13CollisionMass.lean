import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassCollisions
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassSourceDetermined
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassResolvedMass

/-!
# PNP residual-side-information V13 collision/mass subcoverage

This module packages the V13 residual-side-information collision and
resolved-mass layer.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The V13 collision/mass layer: same-source residual variation is not
source-only, source-determined residuals have zero resolving mass and no
advantage, positive advantage forces positive resolving mass, and positive
resolving mass exposes the supported residual obstruction package. -/
def V13ResidualSideInformationCollisionMassSubcoverage : Prop :=
  (∀ {Ω : Type u} {Base : Type v} {Side : Type w} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω},
      base x = base y →
        side x ≠ side y →
          ¬ SideInfoDeterminedBy base side) ∧
  (∀ {Ω : Type u} {Base : Type v} {Side : Type w} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω},
      base x = base y →
        side x ≠ side y →
          ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {Ω : Type u} {Base : Type v} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω},
      base x = base y →
        target x ≠ target y →
          ¬ SourceOnlyBooleanClassifier base target) ∧
  (SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
    ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
    ¬ SourceOnlyPredicateCapturesSideEq
      residualSideInfoToyBase residualSideInfoToySide false ∧
    ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side),
      (∀ x, base (τ x) = base x) →
        SideInfoDeterminedBy base side →
          ∀ x, side (τ x) = side x) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ),
      (∀ x, base (τ x) = base x) →
        SideInfoDeterminedBy base side →
          resolvedMass τ side w = 0) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          SideInfoDeterminedBy base side →
            (∀ x, y (τ x) = !(y x)) →
              (∀ x, w (τ x) = w x) →
                ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                0 < resolvedMass τ side w) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                0 < resolvedMass τ side w) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ),
      (∀ x, base (τ x) = base x) →
        (0 < resolvedMass τ side w ↔
          ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x))) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ),
      (∀ x, base (τ x) = base x) →
        0 < resolvedMass τ side w →
          ¬ SideInfoDeterminedBy base side ∧
            PositiveWeightSideInfoCollisionOverBase base side w ∧
            (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
            (∃ x, 0 < w x ∧
              ¬ SourceOnlyPredicateCapturesSideEq base side (side x)))

@[simp] theorem v13ResidualSideInformationCollisionMassSubcoverage :
    V13ResidualSideInformationCollisionMassSubcoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω Base Side base side x y hbase hside
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_decoder
        hbase hside
  · intro Ω Base Side base side x y hbase hside
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_predicate
        hbase hside
  · intro Ω Base base target x y hbase htarget
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
        hbase htarget
  · exact residualSideInformationCoverage_anchor_toy_collision
  · intro α Base Side _Fintypeα τ base side hbase hdet
    exact
      residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
        τ base side hbase hdet
  · intro α Base Side _Fintypeα τ base side w hbase hdet
    exact
      residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
        τ base side w hbase hdet
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hdet hy hw
    exact
      residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
        τ base side y w h hτ hbase hdet hy hw
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side w hbase
    exact
      residualSideInformationCoverage_anchor_positive_resolvedMass_iff_not_supportwise_visible_pair_invariant
        τ base side w hbase
  · intro α Base Side _Fintypeα τ base side w hbase hmass
    exact
      residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
        τ base side w hbase hmass

end Mettapedia.Computability.PNP
