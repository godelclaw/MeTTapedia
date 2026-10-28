import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesStrictHalf

/-!
# P vs NP crux: residual side-information prediction-separation consequences

Prediction-separation route-coverage consequences for residual side information.
-/

namespace Mettapedia.Computability.PNP

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base must exhibit a supported involution pair where the final
classifier prediction changes. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) :=
  exists_positive_prediction_ne_of_pos_doubledAdvantage_pair_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: the strict half-accuracy formulation yields the same
supported prediction-separation witness. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
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
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) :=
  exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass_pair_invariant_base
    τ base side y w h hτ hbase hy hw hadv

end Mettapedia.Computability.PNP
