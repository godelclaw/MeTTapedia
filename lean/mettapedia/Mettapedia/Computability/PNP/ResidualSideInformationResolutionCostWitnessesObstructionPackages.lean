import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCollapse

/-!
# Residual side-information resolution cost: witness obstruction packages

Classifier-free positive-resolved-mass obstruction packages extracted from residual repair claims.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Any existential positive-advantage residual repair over an invariant base
already collapses to the classifier-free positive-resolving-mass obstruction
package. -/
theorem pos_resolvedMass_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  have hmass :
      0 < resolvedMass τ side w :=
    resolvedMass_pos_of_pos_doubledAdvantage_pair
      τ base side y w h hτ hbase hy hw hadv
  rcases
    pos_resolvedMass_obstruction_package_invariant_base
      τ base side w hbase hmass with
    ⟨hnot, hcollision, hwitness, hpred⟩
  exact ⟨hmass, hnot, hcollision, hwitness, hpred⟩

/-- The same classifier-free positive-resolving-mass reduction holds for
existential strict half-accuracy residual repair claims. -/
theorem pos_resolvedMass_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  rcases hsuccess with ⟨h, hadv⟩
  have hmass :
      0 < resolvedMass τ side w :=
    resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      τ base side y w h hτ hbase hy hw hadv
  rcases
    pos_resolvedMass_obstruction_package_invariant_base
      τ base side w hbase hmass with
    ⟨hnot, hcollision, hwitness, hpred⟩
  exact ⟨hmass, hnot, hcollision, hwitness, hpred⟩

end

end Mettapedia.Computability.PNP
