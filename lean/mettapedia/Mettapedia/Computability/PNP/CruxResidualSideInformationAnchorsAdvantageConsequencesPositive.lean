import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesCore

/-!
# P vs NP crux: residual side-information positive-advantage consequences

Positive-advantage route-coverage consequences for residual side information.
-/

namespace Mettapedia.Computability.PNP

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a positive-weight same-base residual collision. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x :=
  exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a supported residual collision over the base. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w :=
  positiveWeightSideInfoCollisionOverBase_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: positive doubled advantage from `(base, side)` over
an invariant base exposes a supported residual value whose equality predicate
is not source-only. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  exists_positive_not_sourceOnlyPredicateCapturesSideEq_of_pos_doubledAdvantage_invariant_base
    τ base side y w h hτ hbase hy hw hadv

/-- Route-coverage anchor: if every supported residual equality test is
source-only, then `(base, side)` cannot have positive doubled advantage over an
invariant base. -/
theorem residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supported_sourceOnlyPredicateCapturesSideEq_invariant_base
    τ base side y w h hτ hbase hy hw hsource

/-- Route-coverage anchor: if the classifier's positive-support predictions
are already source-only over the invariant base, then syntactically mentioning
the residual side channel cannot create positive doubled advantage. -/
theorem residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h :=
  not_pos_doubledAdvantage_pair_of_supportwiseSourceOnlyPairClassifier_invariant_base
    τ base side y w h hτ hbase hy hw hsource

end Mettapedia.Computability.PNP
