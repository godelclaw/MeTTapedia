import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostSupportedPackagesCore

/-!
# Residual side-information resolution cost: supported packages with visible-balancing blockers

Supported obstruction packages sharpened by the absence of supportwise visible-pair balancing.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- The full supported obstruction package can be sharpened by the generic
visible-pair balancing burden: any existential positive-advantage residual
repair over an invariant base already carries a witness classifier with the
entire supported proof-relevant package and no supportwise visible-pair
balancing involution on the same visible surface. -/
theorem exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases
    exists_classifier_and_supported_obstruction_package_of_exists_pos_doubledAdvantage_invariant_base
      τ base side y w hτ hbase hy hw hsuccess with
    ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep⟩
  refine ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep, ?_⟩
  exact
    not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
      base side y w h hadv

/-- The same sharpening holds for existential strict half-accuracy residual
repair claims. -/
theorem exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases
    exists_classifier_and_supported_obstruction_package_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
      τ base side y w hτ hbase hy hw hsuccess with
    ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep⟩
  refine ⟨h, hadv, hmass, hnot, hsource, hwitness, hpred, hsep, ?_⟩
  exact
    not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
      base side y w h hadv

/-- Exact existential boundary sharpened all the way to the full supported
proof-relevant package: over an invariant base, positive-advantage residual
repair is exactly the same claim plus the supported obstruction package and
absence of supportwise visible-pair balancing. -/
theorem exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact existential boundary sharpened in the same way for strict
half-accuracy residual repair. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_supported_obstruction_package_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hpackage
    rcases hpackage with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

end

end Mettapedia.Computability.PNP
