import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassCollisions
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassSourceDetermined
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassResolvedMass

/-!
# Regression checks for PNP residual-side-information anchors: basic residual collisions and resolved-mass checks

This module is part of the decomposed residual-side-information regression
ledger.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while separating residual-anchor checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_collision_blocks_source_decoder_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_decoder
      hbase hside

theorem residual_side_information_anchor_collision_blocks_source_predicate_regression
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_predicate
      hbase hside

theorem residual_side_information_anchor_collision_blocks_source_boolean_classifier_regression
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target := by
  exact
    residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
      hbase htarget

theorem residual_side_information_anchor_toy_collision_regression :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SourceOnlyPredicateCapturesSideEq
        residualSideInfoToyBase residualSideInfoToySide false ∧
      ¬ SourceOnlyBooleanClassifier
      residualSideInfoToyBase residualSideInfoToySide := by
  exact residualSideInformationCoverage_anchor_toy_collision

theorem residual_side_information_anchor_source_determined_invariant_unresolved_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x := by
  exact
    residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
      τ base side hbase hdet

theorem residual_side_information_anchor_source_determined_zero_resolvedMass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 := by
  exact
    residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
      τ base side w hbase hdet

theorem residual_side_information_anchor_source_determined_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
      τ base side y w h hτ hbase hdet hy hw

theorem residual_side_information_anchor_positive_advantage_positive_resolved_mass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_positive_resolved_mass_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_resolved_mass_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_witnesses_same_base_residual_collision
      τ base side w hbase hmass

theorem residual_side_information_anchor_positive_resolved_mass_iff_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_iff_same_base_residual_collision
      τ base side w hbase

theorem residual_side_information_anchor_positive_resolved_mass_iff_not_supportwise_visible_pair_invariant_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_iff_not_supportwise_visible_pair_invariant
      τ base side w hbase

theorem residual_side_information_anchor_positive_resolved_mass_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
      τ base side w hbase hmass

end Mettapedia.Computability.PNP.CruxSynthesisRegression
