import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantCore

/-!
# Residual side-information resolution cost: positive mass

Positive orbit-resolving mass over an invariant base exposes residual collision data and classifier-free obstruction packages.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already exposes a positive-weight residual collision over the base. -/
theorem positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
    ⟨x, hxw, hside⟩
  exact ⟨x, τ x, hxw, (hbase x).symm, fun hside' => hside hside'.symm⟩

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already rules out source-only residual decoding. -/
theorem not_sideInfoDeterminedBy_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass)

/-- Positive orbit-resolving mass for an invariant-base residual side channel
already exposes a supported residual value whose equality predicate is not
source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_resolvedMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass)

/-- Positive orbit-resolving mass is already a classifier-free residual-side
obstruction over an invariant base.  It simultaneously rules out source-only
residual decoding, exhibits a supported same-base residual collision, and
exposes a supported residual equality test that is not source-only. -/
theorem pos_resolvedMass_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x)
    (hmass : 0 < resolvedMass τ side w) :
    ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  have hcollision :
      PositiveWeightSideInfoCollisionOverBase base side w :=
    positiveWeightSideInfoCollisionOverBase_of_pos_resolvedMass_invariant_base
      τ base side w hbase hmass
  rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
    ⟨x, hxw, hside⟩
  refine ⟨?_, hcollision, ?_, ?_⟩
  · exact not_sideInfoDeterminedBy_of_positiveWeight_collision hcollision
  · exact ⟨x, hxw, hbase x, hside⟩
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
        hcollision

/-- Over an invariant base, positive orbit-resolving mass is exactly the same
as a positive-support same-base involution pair where the residual side
information changes. -/
theorem pos_resolvedMass_iff_exists_positive_same_base_ne_side_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · intro hmass
    rcases exists_resolving_point_of_pos_resolvedMass τ side w hmass with
      ⟨x, hxw, hside⟩
    exact ⟨x, hxw, hbase x, hside⟩
  · rintro ⟨x, hxw, _hbase, hside⟩
    exact resolvedMass_pos_of_resolving_point τ side w hxw hside

end

end Mettapedia.Computability.PNP
