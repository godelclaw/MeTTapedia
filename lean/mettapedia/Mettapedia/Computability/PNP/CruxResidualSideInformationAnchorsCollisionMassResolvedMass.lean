import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassSourceDetermined

/-!
# PNP residual-side-information anchors: positive resolved mass

This module collects consequences and characterizations of positive
orbit-resolving mass over an invariant base.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- Route-coverage anchor: any positive doubled advantage from `(base, side)`
over an invariant base already forces strictly positive orbit-resolving mass
for the residual side information. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w :=
  resolvedMass_pos_of_pos_doubledAdvantage_pair
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation likewise forces
strictly positive orbit-resolving mass for the residual side information. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
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
    0 < resolvedMass τ side w :=
  resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: once residual side information carries positive
orbit-resolving mass over an invariant base, some positive-weight involution
pair must already differ in residual value while agreeing on the base. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_witnesses_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  obtain ⟨x, hxw, hside⟩ := exists_resolving_point_of_pos_resolvedMass τ side w hmass
  exact ⟨x, hxw, hbase x, hside⟩

/-- Route-coverage anchor: over an invariant base, positive orbit-resolving
mass is exactly equivalent to a positive-support same-base involution pair
where the residual side information changes. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_iff_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    pos_resolvedMass_iff_exists_positive_same_base_ne_side_invariant_base
      τ base side w hbase

/-- Route-coverage anchor: over an invariant base, positive orbit-resolving
mass is exactly equivalent to failure of supportwise invariance of the visible
`(base, side)` pair on positive support. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_iff_not_supportwise_visible_pair_invariant
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    pos_resolvedMass_iff_not_supportwise_visiblePair_invariant_invariant_base
      τ base side w hbase

/-- Route-coverage anchor: positive orbit-resolving mass over an invariant base
is already a pure residual-side-information obstruction package, before any
classifier-specific prediction facts are used. -/
theorem residualSideInformationCoverage_anchor_positive_resolvedMass_forces_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) :=
  pos_resolvedMass_obstruction_package_invariant_base
    τ base side w hbase hmass

end Mettapedia.Computability.PNP
