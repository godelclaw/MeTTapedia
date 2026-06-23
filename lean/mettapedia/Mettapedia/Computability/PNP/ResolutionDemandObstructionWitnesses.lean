import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction

/-!
# P vs NP crux: resolving-point witnesses

This module turns positive advantage or positive orbit-resolving mass into an
explicit positive-weight point where the residual side channel changes across
the involution.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- Equivalently, every positive doubled advantage witnesses positive
orbit-resolving side-channel mass. -/
theorem resolvedMass_pos_of_pos_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  have hle :
      doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w :=
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw
  omega

/-- Positive orbit-resolving mass exposes a positive-weight point where the
side-channel value changes across the involution. -/
theorem exists_resolving_point_of_pos_resolvedMass
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hmass : 0 < resolvedMass τ v w) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  classical
  by_contra hnone
  have hunresolved : ∀ x, 0 < w x → v (τ x) = v x := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  have hzero := resolvedMass_eq_zero_of_supportwise_unresolved τ v w hunresolved
  omega

/-- Conversely, one positive-weight point where the side channel changes across
the involution already gives positive orbit-resolving mass. -/
theorem resolvedMass_pos_of_resolving_point
    (τ : α → α) (v : α → V) (w : α → ℕ)
    {x : α} (hx : 0 < w x) (hchange : v (τ x) ≠ v x) :
    0 < resolvedMass τ v w := by
  classical
  unfold resolvedMass outsideMass sliceMass
  let x' : {a : α // ¬ unresolvedBySideChannel τ v a} :=
    ⟨x, by
      dsimp [unresolvedBySideChannel]
      exact hchange⟩
  have hle :
      w x ≤ ∑ y : {a : α // ¬ unresolvedBySideChannel τ v a}, w y.1 := by
    simpa [x'] using
      (Finset.single_le_sum
        (f := fun y : {a : α // ¬ unresolvedBySideChannel τ v a} => w y.1)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x'))
  exact lt_of_lt_of_le hx hle

/-- Every strict half-accuracy advantage from an invariant feature plus
residual side channel exposes a positive-weight point where the side channel
changes across the involution. -/
theorem exists_resolving_point_of_total_lt_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_resolvedMass τ v w
    (resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
      τ u v y w h hτ hu hy hw hadv)

/-- Every positive doubled advantage from an invariant feature plus residual
side channel exposes a positive-weight point where the side channel changes
across the involution. -/
theorem exists_resolving_point_of_pos_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x :=
  exists_resolving_point_of_pos_resolvedMass τ v w
    (resolvedMass_pos_of_pos_doubledAdvantage_pair
      τ u v y w h hτ hu hy hw hadv)

end

end Mettapedia.Computability.PNP
