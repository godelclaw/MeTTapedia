import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostAdvantageSourceDetermination

/-!
# Residual side-information resolution cost: positive advantage witnesses

Positive doubled advantage exposes same-base residual changes, collision data, and non-source-only residual equality tests.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight same-base point where the residual side information
changes across the involution. -/
theorem exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases
    exists_resolving_point_of_pos_doubledAdvantage_pair
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hside⟩
  exact ⟨x, hxw, hbase x, hside⟩

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight residual collision over the base. -/
theorem positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  rcases
    exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hbase_x, hside_x⟩
  exact ⟨x, τ x, hxw, hbase_x.symm, fun hside => hside_x hside.symm⟩

/-- Positive doubled advantage from `(base, side)` over an invariant base
exposes a positive-weight residual value whose equality test is not
source-only. -/
theorem exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_positiveWeight_collision
    (positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv)

/-- If every positive-weight residual equality test is source-only, then
`(base, side)` cannot have positive doubled advantage over an invariant base. -/
theorem not_pos_doubledAdvantage_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  intro hadv
  rcases
    exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
      τ base side y w h hτ hbase hy hw hadv with
    ⟨x, hxw, hnot⟩
  exact hnot (hsource x hxw)

end

end Mettapedia.Computability.PNP
