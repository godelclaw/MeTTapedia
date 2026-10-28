import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCore

/-!
# Residual side-information resolution cost: source-only classifiers

Supportwise source-only classifier invariance, advantage blockers, and prediction-separation witnesses over invariant bases.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

omit [Fintype α] in
/-- A source-only pair classifier on positive support has the same prediction
on every positive-weight involution pair when the base is invariant. -/
theorem prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ∀ x, 0 < w x →
      h (base (τ x), side (τ x)) = h (base x, side x) := by
  rcases hsource with ⟨classifier, hclassifier⟩
  intro x hx
  have hxτ : 0 < w (τ x) := by
    simpa [hw x] using hx
  calc
    h (base (τ x), side (τ x)) = classifier (base (τ x)) :=
      (hclassifier (τ x) hxτ).symm
    _ = classifier (base x) := by rw [hbase x]
    _ = h (base x, side x) := hclassifier x hx

/-- If the classifier's realized positive-support predictions are already
source-only over the invariant base, then `(base, side)` cannot have positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_of_supportwise_prediction_invariant
    τ (fun x => (base x, side x)) y w h hτ hy hw
    (prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      τ base side w h hbase hw hsource)

/-- In the strict half-accuracy formulation, source-only realized predictions
on positive support cannot beat chance over an invariant base. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h :=
  not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
    τ (fun x => (base x, side x)) y w h hτ hy hw
    (prediction_eq_under_involution_of_supportwiseSourceOnlyPairClassifier_invariant_base
      τ base side w h hbase hw hsource)

/-- Any positive doubled advantage from `(base, side)` over an invariant base
forces a positive-weight involution pair where the final classifier's
prediction changes. -/
theorem exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  let _ := hbase
  exact
    exists_positive_prediction_ne_of_pos_doubledAdvantage
      τ (fun x => (base x, side x)) y w h hτ hy hw hadv

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
forces the same supported prediction-separation witness. -/
theorem exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  let _ := hbase
  exact
    exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass
      τ (fun x => (base x, side x)) y w h hτ hy hw hadv

end

end Mettapedia.Computability.PNP
