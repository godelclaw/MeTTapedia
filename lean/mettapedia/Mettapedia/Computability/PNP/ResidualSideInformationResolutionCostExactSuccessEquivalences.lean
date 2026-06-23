import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostExactSuccessPackages

/-!
# Residual side-information resolution cost: exact-success equivalences

Equivalence boundaries for exact supported success and full residual-resolution budget packages.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Positive-support exact supported success on an invariant-base residual
surface is exactly equivalent to existence of a witness classifier carrying the
full supported obstruction package, a saturated resolution budget, and the
generic no-visible-pair-balancing burden. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_exact_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
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
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      exact_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hpackage
    rcases hpackage with
      ⟨h, hperfect, _hadv, _hbudget, hmass, _hnot, _hsource, _hwitness, _hpred,
        _hsep, _hbalancing⟩
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

/-- Positive-support exact supported success on an invariant-base residual
surface is exactly equivalent to existence of a witness classifier whose
doubled advantage saturates the full orbit-resolving budget, together with the
same supported obstruction package and no-visible-pair-balancing burden. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
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
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hpackage
    rcases hpackage with
      ⟨h, hbudget, hfull, hmass, _hnot, _hsource, _hwitness, _hpred, _hsep,
        _hbalancing⟩
    have hperfect :
        weightedCorrectMass (fun x => (base x, side x)) y w h =
          weightedTotalMass w :=
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        (fun x => (base x, side x)) y w h (hbudget.trans hfull)
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

/-- Exact minimal proof-relevant boundary: over an invariant base, nonempty
exact supported success is exactly equivalent to existence of a classifier that
spends the full orbit-resolving budget and thereby exposes a supported
same-base residual witness. -/
theorem exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        resolvedMass τ side w = weightedTotalMass w ∧
        0 < resolvedMass τ side w ∧
        (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) := by
  constructor
  · rintro ⟨⟨h, hperfect⟩, htotal⟩
    refine ⟨h, ?_⟩
    exact
      full_resolution_budget_and_same_base_residual_witness_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect htotal
  · intro hwitness
    rcases hwitness with ⟨h, hbudget, hfull, hmass, _hwitness⟩
    have hperfect :
        weightedCorrectMass (fun x => (base x, side x)) y w h =
          weightedTotalMass w :=
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        (fun x => (base x, side x)) y w h (hbudget.trans hfull)
    refine ⟨⟨h, hperfect⟩, ?_⟩
    exact lt_of_lt_of_le hmass (resolvedMass_le_weightedTotalMass τ side w)

end

end Mettapedia.Computability.PNP
