import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCollapse

/-!
# Residual side-information resolution cost: visible-balancing witness boundaries

Proof-relevant residual witnesses sharpened by the absence of supportwise visible-pair balancing.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Any existential positive-advantage residual repair over an invariant base
already exposes the minimal resolving witness and also rules out any
supportwise visible-pair balancing involution on the same visible surface. -/
theorem exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
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
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
        base side y w h hadv

/-- The same sharpening holds for existential strict half-accuracy residual
repair claims. -/
theorem exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
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
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv
  · exact
      not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
        base side y w h hadv

/-- Exact minimal boundary sharpened by the balancing obstruction: over an
invariant base, existential positive-advantage repair is equivalent to the
same claim plus a resolving witness and absence of supportwise visible-pair
balancing. -/
theorem exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
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
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact minimal boundary sharpened by the same balancing obstruction for the
strict half-accuracy formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
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
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

end

end Mettapedia.Computability.PNP
