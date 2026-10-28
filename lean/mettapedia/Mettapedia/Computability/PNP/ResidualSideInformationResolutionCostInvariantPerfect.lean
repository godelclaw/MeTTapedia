import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantVisiblePair

/-!
# Residual side-information resolution cost: perfect correctness

Perfect supported correctness over an invariant base forces full residual budget and visible-pair separation.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- If a classifier on `(base, side)` is correct on every positive-weight
point over an invariant base, then all supported mass is orbit-resolving
mass. -/
theorem resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) :
    resolvedMass τ side w = weightedTotalMass w :=
  resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    τ base side y w h hτ hbase hy hw hperfect

/-- Perfect supported correctness on `(base, side)` over an invariant base
forces supportwise separation of the visible pair on every positive-weight
involution pair. -/
theorem supportwise_visiblePair_separated_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) :
    ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
      τ base side w hbase).1
      (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_invariant_base
        τ base side y w h hτ hbase hy hw hperfect)

end

end Mettapedia.Computability.PNP
