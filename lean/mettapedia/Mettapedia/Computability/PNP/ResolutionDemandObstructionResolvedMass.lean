import Mettapedia.Computability.PNP.ResolutionDemandObstructionPairBounds

/-!
# P vs NP crux: resolved-mass equivalences

This module records when orbit-resolving mass is zero, total, or exactly tied
to supported correctness on an invariant-feature-plus-residual classifier.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- If a residual side channel is unresolved everywhere, its resolved mass is
zero. -/
theorem resolvedMass_eq_zero_of_unresolved
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hunresolved : ∀ x, v (τ x) = v x) :
    resolvedMass τ v w = 0 := by
  classical
  unfold resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro x _
  exfalso
  exact x.2 (by
    dsimp [unresolvedBySideChannel]
    exact hunresolved x.1)

/-- If a residual side channel is unresolved on every positive-weight point,
its resolved mass is zero. -/
theorem resolvedMass_eq_zero_of_supportwise_unresolved
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    resolvedMass τ v w = 0 := by
  classical
  unfold resolvedMass outsideMass sliceMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : 0 < w x.1
  · exfalso
    exact x.2 (by
      dsimp [unresolvedBySideChannel]
      exact hunresolved x.1 hx)
  · have hx0 : w x.1 = 0 := Nat.eq_zero_of_not_pos hx
    simp [hx0]

/-- Resolved mass is bounded by the total supported mass. -/
theorem resolvedMass_le_weightedTotalMass
    (τ : α → α) (v : α → V) (w : α → ℕ) :
    resolvedMass τ v w ≤ weightedTotalMass w := by
  classical
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := unresolvedBySideChannel τ v)
      (w := w)
  unfold resolvedMass
  omega

/-- If a residual side channel changes across every positive-weight involution
pair, then all supported mass is orbit-resolving mass. -/
theorem resolvedMass_eq_weightedTotalMass_of_supportwise_resolving
    (τ : α → α) (v : α → V) (w : α → ℕ)
    (hresolve : ∀ x, 0 < w x → v (τ x) ≠ v x) :
    resolvedMass τ v w = weightedTotalMass w := by
  classical
  have hslice :
      sliceMass (unresolvedBySideChannel τ v) w = 0 := by
    unfold sliceMass
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : 0 < w x.1
    · exfalso
      exact hresolve x.1 hx x.2
    · exact Nat.eq_zero_of_not_pos hx
  have hsplit :=
    weightedTotalMass_eq_slice_add_outside
      (p := unresolvedBySideChannel τ v)
      (w := w)
  unfold resolvedMass
  simpa [hslice] using hsplit.symm

/-- The orbit-resolving mass is all supported mass exactly when the side
channel changes across every positive-weight involution pair. -/
theorem resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving
    (τ : α → α) (v : α → V) (w : α → ℕ) :
    resolvedMass τ v w = weightedTotalMass w ↔
      ∀ x, 0 < w x → v (τ x) ≠ v x := by
  constructor
  · intro hmass x hxw hside
    classical
    let p : α → Prop := unresolvedBySideChannel τ v
    have hsplit :
        weightedTotalMass w = sliceMass p w + resolvedMass τ v w := by
      unfold resolvedMass outsideMass
      simpa [p] using
        weightedTotalMass_eq_slice_add_outside (p := p) (w := w)
    have hzero : sliceMass p w = 0 := by
      omega
    let x' : {a : α // p a} := ⟨x, by simpa [p, unresolvedBySideChannel] using hside⟩
    have hle' :
        w x'.1 ≤ ∑ y : {a : α // p a}, w y.1 := by
      exact
        Finset.single_le_sum
          (f := fun y : {a : α // p a} => w y.1)
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ x')
    have hle :
        w x ≤ ∑ y : {a : α // p a}, w y.1 := by
      simpa [x'] using hle'
    unfold sliceMass at hzero
    have hle0 : w x ≤ 0 := by
      simpa [hzero] using hle
    omega
  · intro hresolve
    exact resolvedMass_eq_weightedTotalMass_of_supportwise_resolving τ v w hresolve

/-- If a classifier on `(u, v)` is correct on every positive-weight point,
then the residual side channel must resolve all supported involution pairs. -/
theorem resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    resolvedMass τ v w = weightedTotalMass w := by
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  have hupper : resolvedMass τ v w ≤ weightedTotalMass w :=
    resolvedMass_le_weightedTotalMass τ v w
  omega

/-- Perfect supported correctness on `(u, v)` forces the side channel to
change across every positive-weight involution pair. -/
theorem supportwise_resolving_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    ∀ x, 0 < w x → v (τ x) ≠ v x := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ v w).1
      (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
        τ u v y w h hτ hu hy hw hperfect)

/-- Under exact total correctness on an invariant-pair feature surface, the
classifier's doubled advantage is exactly the orbit-resolving mass. -/
theorem doubledAdvantage_eq_resolvedMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hperfect :
      weightedCorrectMass (fun x => (u x, v x)) y w h =
        weightedTotalMass w) :
    doubledAdvantage (fun x => (u x, v x)) y w h = resolvedMass τ v w := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
    (fun x => (u x, v x)) y w h hperfect]
  exact
    (resolvedMass_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass_pair
      τ u v y w h hτ hu hy hw hperfect).symm

end

end Mettapedia.Computability.PNP
