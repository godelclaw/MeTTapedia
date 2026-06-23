import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPrediction

/-!
# P vs NP crux: residual side-information supported-package consequences

Supported obstruction package consequences for residual side-information advantage claims.
-/

namespace Mettapedia.Computability.PNP

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base is not a weak residual repair.  It simultaneously forces
strictly positive residual resolved mass, makes the residual side information
non-source-determined, blocks any positive-support source-only classifier
description, and exposes supported same-base residual variation, a supported
non-source-only residual equality test, and supported prediction separation. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_supported_obstruction_package
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation forces the same
residual-side-information obstruction package.  Beating half accuracy with
`(base, side)` over an invariant base already requires strictly positive
resolved mass, supported non-source residual variation, and supported
prediction separation. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_supported_obstruction_package
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
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro hsource
    exact
      (residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource) hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_witnesses_same_base_residual_collision
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · exact
      residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

end Mettapedia.Computability.PNP
