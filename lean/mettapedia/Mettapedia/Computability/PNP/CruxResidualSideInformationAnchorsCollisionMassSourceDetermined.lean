import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassCollisions

/-!
# PNP residual-side-information anchors: source-determined residual collapse

This module isolates the consequences of residual side information being
decoded from an involution-invariant source summary.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- Route-coverage anchor: if residual side information is decoded from an
involution-invariant base feature, then it is itself unresolved across the
involution. -/
theorem residualSideInformationCoverage_anchor_source_determined_invariant_unresolved
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    ∀ x, side (τ x) = side x :=
  side_eq_under_involution_of_determinedBy_invariant_base
    τ base side hbase hdet

/-- Route-coverage anchor: source-determined residual side information over an
invariant base has zero orbit-resolving mass. -/
theorem residualSideInformationCoverage_anchor_source_determined_zero_resolvedMass
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side) :
    resolvedMass τ side w = 0 :=
  resolvedMass_eq_zero_of_determinedBy_invariant_base
    τ base side w hbase hdet

/-- Route-coverage anchor: source-determined residual side information over an
invariant base cannot supply positive doubled advantage. -/
theorem residualSideInformationCoverage_anchor_source_determined_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hdet : SideInfoDeterminedBy base side)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
    τ base side y w h hτ hbase hdet hy hw

end Mettapedia.Computability.PNP
