import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchActiveOrbit
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchSupportedBudget
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchFork

/-!
# P vs NP crux: residual side-information source and visible-pair consequences

Basic positive and strict-half route-coverage consequences for source determination and visible-pair asymmetry.
-/

namespace Mettapedia.Computability.PNP

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base proves the residual side information is not source-derived. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base must already break supportwise invariance of the visible
`(base, side)` pair on positive support. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forces_visible_pair_asymmetry
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    (residualSideInformationCoverage_anchor_positive_resolvedMass_iff_not_supportwise_visible_pair_invariant
      τ base side w hbase).1
      (residualSideInformationCoverage_anchor_positive_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv)

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base also proves the residual side information is not
source-derived. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
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
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from `(base, side)`
over an invariant base likewise must already break supportwise invariance of
the visible `(base, side)` pair on positive support. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forces_visible_pair_asymmetry
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
    ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    (residualSideInformationCoverage_anchor_positive_resolvedMass_iff_not_supportwise_visible_pair_invariant
      τ base side w hbase).1
      (residualSideInformationCoverage_anchor_strict_half_advantage_forces_positive_resolvedMass
        τ base side y w h hτ hbase hy hw hadv)

end Mettapedia.Computability.PNP
