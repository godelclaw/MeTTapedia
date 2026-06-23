import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingFiberImbalance

/-!
# Residual side-information resolution cost: classifier-free collapse

Existential visible-success claims collapse to positive residual mass plus a concrete imbalanced visible-pair fiber.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Any existential positive-advantage residual repair over an invariant base
already collapses to classifier-free data: positive resolved mass together
with a concrete imbalanced visible `(base, side)` fiber. -/
theorem pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_pos_doubledAdvantage_invariant_base
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_visiblePair_fiber_imbalance_of_pos_doubledAdvantage
        base side y w h hadv

/-- The same classifier-free collapse holds for existential strict-half
weighted success. -/
theorem pos_resolvedMass_and_exists_visiblePair_fiber_imbalance_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    [Fintype Base] [Fintype Side] [DecidableEq Base] [DecidableEq Side]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_visiblePair_fiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
        base side y w h hadv

end

end Mettapedia.Computability.PNP
