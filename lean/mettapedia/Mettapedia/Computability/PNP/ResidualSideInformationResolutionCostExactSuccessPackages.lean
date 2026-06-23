import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostSupportedPackagesCore
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostSupportedPackagesNoVisiblePairBalancing

/-!
# Residual side-information resolution cost: exact-success packages

Exact-success hypotheses repackaged as full residual-resolution budget and supported obstruction data.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Positive-support exact success on `(base, side)` over an invariant base
already carries the full supported obstruction package, saturates the whole
resolution budget, and rules out any supportwise visible-pair balancing
involution on the same visible surface. -/
theorem exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w ∧
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  have hadv :
      0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
    rw [doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
      (fun x => (base x, side x)) y w h hperfect]
    exact htotal
  have hbudget :
      doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w :=
    doubledAdvantage_eq_resolvedMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
      τ base side y w h hτ hbase hy hw hperfect
  have hmass :
      0 < resolvedMass τ side w := by
    rw [← hbudget]
    exact hadv
  have hnot :
      ¬ SideInfoDeterminedBy base side :=
    not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv
  have hsource :
      ¬ SupportwiseSourceOnlyPairClassifier base side w h := by
    intro hsource
    exact
      (not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
        τ base side y w h hτ hbase hy hw hsource) hadv
  refine ⟨hperfect, hadv, hbudget, hmass, hnot, hsource, ?_, ?_, ?_, ?_⟩
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        base side y w h hadv

/-- The same exact-success hypothesis can be repackaged purely in terms of the
full resolving budget it forces, together with the supported obstruction data
on the visible surface. -/
theorem full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      resolvedMass τ side w = weightedTotalMass w ∧
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
    exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect htotal with
    ⟨_hperfect, _hadv, hbudget, hmass, hnot, hsource, hwitness, hpred, hsep,
      hbalancing⟩
  have hfull :
      resolvedMass τ side w = weightedTotalMass w :=
    resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect
  exact ⟨hbudget, hfull, hmass, hnot, hsource, hwitness, hpred, hsep, hbalancing⟩

/-- The exact-success boundary also has a minimal proof-relevant reading: exact
supported success forces the full resolving budget together with a supported
same-base residual witness. -/
theorem full_resolution_budget_and_same_base_residual_witness_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w)
    (htotal : 0 < weightedTotalMass w) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
        resolvedMass τ side w ∧
      resolvedMass τ side w = weightedTotalMass w ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) := by
  rcases
    full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
      τ base side y w h hτ hbase hy hw hperfect htotal with
    ⟨hbudget, hfull, hmass, _hnot, _hsource, hwitness, _hpred, _hsep,
      _hbalancing⟩
  exact ⟨hbudget, hfull, hmass, hwitness⟩

end

end Mettapedia.Computability.PNP
