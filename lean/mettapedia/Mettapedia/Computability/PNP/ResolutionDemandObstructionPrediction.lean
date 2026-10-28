import Mettapedia.Computability.PNP.ResolutionDemandObstructionResolvedMass

/-!
# P vs NP crux: prediction invariance obstruction

If the final Boolean prediction remains invariant on supported involution
pairs, it cannot carry positive doubled advantage.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- A supportwise-unresolved residual side channel cannot support positive
doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwise_unresolved
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact
    not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
      τ u v y w h hτ hu hy hw
      (resolvedMass_eq_zero_of_supportwise_unresolved τ v w hunresolved)

/-- If the final Boolean prediction is involution-invariant on all
positive-weight points, then it cannot beat half accuracy.  This blocks a
repair where a classifier syntactically uses a side channel but its realized
predictions on support still factor through an invariant source summary. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x)) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  classical
  let p : α → Prop := fun x => 0 < w x
  let pred : α → Bool := fun x => h (u x)
  have hp : ∀ x, p x → p (τ x) := by
    intro x hx
    dsimp [p] at hx ⊢
    simpa [hw x] using hx
  have hpred_inv : ∀ x, p x → pred (τ x) = pred x := by
    intro x hx
    dsimp [p] at hx
    exact hpred x hx
  have hsupport : ∀ x, 0 < w x → p x := by
    intro x hx
    exact hx
  have hno :
      ¬ weightedTotalMass w <
        2 * weightedCorrectMass pred y w (fun b : Bool => b) :=
    not_total_lt_two_mul_weightedCorrectMass_of_support_subset
      τ p pred y w (fun b : Bool => b) hτ hp hpred_inv
      (fun x _ => hy x) (fun x _ => hw x) hsupport
  have hmass :
      weightedCorrectMass pred y w (fun b : Bool => b) =
        weightedCorrectMass u y w h := by
    rfl
  intro hadv
  exact hno (by simpa [hmass] using hadv)

/-- Positive doubled advantage is impossible under the same supportwise
prediction-invariance condition. -/
theorem not_pos_doubledAdvantage_of_supportwise_prediction_invariant
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x)) :
    ¬ 0 < doubledAdvantage u y w h := by
  intro hadv
  have hno :=
    not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred
  have hlt : weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
    unfold doubledAdvantage at hadv
    omega
  exact hno hlt

/-- Any positive doubled advantage must be witnessed by a positive-weight
involution pair where the final prediction actually changes. -/
theorem exists_positive_prediction_ne_of_pos_doubledAdvantage
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage u y w h) :
    ∃ x, 0 < w x ∧ h (u (τ x)) ≠ h (u x) := by
  by_contra hnone
  have hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x) := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  exact
    (not_pos_doubledAdvantage_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred) hadv

/-- The same prediction-separation witness follows from strict half-accuracy
advantage. -/
theorem exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ x, 0 < w x ∧ h (u (τ x)) ≠ h (u x) := by
  by_contra hnone
  have hpred : ∀ x, 0 < w x → h (u (τ x)) = h (u x) := by
    intro x hx
    by_contra hneq
    exact hnone ⟨x, hx, hneq⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      τ u y w h hτ hy hw hpred) hadv

end

end Mettapedia.Computability.PNP
