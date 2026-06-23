import Mettapedia.Computability.PNP.ResolutionDemandObstructionAdvantage

/-!
# P vs NP crux: pair advantage bounds

Invariant-feature classifiers can only obtain doubled advantage from orbit mass
where the residual side channel resolves an involution pair.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- Any doubled success advantage achieved using an invariant feature map plus
side channel is bounded by the mass where the side channel resolves involution
pairs. -/
theorem doubledAdvantage_pair_le_resolvedMass
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w := by
  unfold doubledAdvantage
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  omega

/-- A claimed doubled advantage of at least `δ` forces at least `δ` units of
orbit-resolving side-channel mass. -/
theorem resolvedMass_ge_of_le_doubledAdvantage_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      δ ≤ doubledAdvantage (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w :=
  le_trans hδ <|
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw

/-- A direct half-accuracy form: if the classifier using an invariant feature
plus residual side channel beats chance by `δ`, then the residual side channel
must resolve at least `δ` units of orbit mass. -/
theorem resolvedMass_ge_of_total_plus_delta_le_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool) (δ : ℕ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hδ :
      weightedTotalMass w + δ ≤
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    δ ≤ resolvedMass τ v w := by
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  omega

/-- Strict success above half accuracy forces positive orbit-resolving
side-channel mass. -/
theorem resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    0 < resolvedMass τ v w := by
  have hle :
      1 ≤ resolvedMass τ v w :=
    resolvedMass_ge_of_total_plus_delta_le_two_mul_weightedCorrectMass_pair
      τ u v y w h 1 hτ hu hy hw (by omega)
  omega

/-- If a residual side channel resolves no involution-paired mass, then it
cannot support any positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_resolvedMass_eq_zero
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hres : resolvedMass τ v w = 0) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  have hle :
    doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w :=
    doubledAdvantage_pair_le_resolvedMass τ u v y w h hτ hu hy hw
  omega

end

end Mettapedia.Computability.PNP
