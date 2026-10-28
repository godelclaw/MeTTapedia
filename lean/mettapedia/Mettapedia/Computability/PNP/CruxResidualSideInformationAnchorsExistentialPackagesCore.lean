import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesNoVisiblePairBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesFiberImbalance

/-!
# PNP residual-side-information anchors: existential package extraction

This module collects the first package-extraction consequences for existential
positive-advantage and strict-half residual repairs over an invariant base.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: before asking for any classifier-specific
prediction-separation witness, an existential positive-advantage residual
repair already collapses to the pure positive-resolving-mass obstruction
package. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_pure_residual_obstruction_package
    {α Base Side : Type*} [Fintype α]
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
  exact
    pos_resolvedMass_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

/-- Route-coverage anchor: an existential positive-advantage residual repair
over an invariant base already yields the full supported obstruction package
with a concrete witness classifier. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

/-- Route-coverage anchor: the same existential proof-relevant obstruction
package holds for strict half-accuracy residual repair claims. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

/-- Route-coverage anchor: the strict half-accuracy existential repair claim
likewise collapses to the pure positive-resolving-mass obstruction package
before any classifier-specific prediction witness is used. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_pure_residual_obstruction_package
    {α Base Side : Type*} [Fintype α]
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
  exact
    pos_resolvedMass_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w hτ hbase hy hw hsuccess

end Mettapedia.Computability.PNP
