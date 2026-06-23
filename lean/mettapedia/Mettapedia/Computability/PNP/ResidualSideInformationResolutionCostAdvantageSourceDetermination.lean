import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantPerfect

/-!
# Residual side-information resolution cost: source-determination blockers

Positive advantage and strict half-accuracy cannot coexist with source-determined residual side information over an invariant base.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Positive doubled advantage from `(base, side)` over an invariant base proves
that the residual side information is not source-determined. -/
theorem not_sideInfoDeterminedBy_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  intro hdet
  exact
    (not_pos_doubledAdvantage_pair_of_determinedBy_invariant_base
      τ base side y w h hτ hbase hdet hy hw) hadv

/-- Strict half-accuracy advantage from `(base, side)` over an invariant base
also proves that the residual side information is not source-determined. -/
theorem not_sideInfoDeterminedBy_of_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  intro hdet
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_determinedBy_invariant_base
      τ base side y w h hτ hbase hdet hy hw) hadv

end

end Mettapedia.Computability.PNP
