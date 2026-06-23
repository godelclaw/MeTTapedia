import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostWitnessesCore
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostWitnessesNoVisiblePairBalancing
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostWitnessesObstructionPackages

/-!
# Residual side-information resolution cost: supported obstruction packages

Proof-relevant supported obstruction packages extracted from residual repair claims.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Any existential positive-advantage residual repair over an invariant base
already yields the full supported obstruction package with an actual witness
classifier. -/
theorem exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
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
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- The same existential proof-relevant package holds for strict half-accuracy
residual repair claims over an invariant base. -/
theorem exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
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
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- Exact existential boundary: over an invariant base, claiming that some
classifier on `(base, side)` has positive doubled advantage is equivalent to
claiming that some classifier realizes the full supported obstruction package. -/
theorem exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
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
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact existential boundary for the strict half-accuracy formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
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
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

end

end Mettapedia.Computability.PNP
