import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction

/-!
# Kpoly feature-route and weakness boundary

This module upgrades the polynomial-image shortcut obstruction to an arbitrary
feature-map boundary.  A feature encoding can realize every full exact-visible
Boolean rule exactly when it separates the exact-visible surface.  On the
weakness side, any feature classifier with positive advantage must separate a
positive-weight involution pair.
-/

namespace Mettapedia.Computability.PNP

universe u v w

section FeatureReadout

variable {Input : Type u} {Feature : Type v}

/-- Boolean classifiers obtained by reading an input only through a feature
map. -/
def featureReadoutFamily (featureOf : Input → Feature) :
    IndexedPredictorFamily (Feature → Bool) Input where
  predict h := fun x => h (featureOf x)

/-- The feature readout image is bounded by the Boolean classifier space on
the feature type. -/
theorem featureReadoutFamily_finitePredictorCover_card
    [Fintype Feature] (featureOf : Input → Feature) :
    (featureReadoutFamily featureOf).FinitePredictorCover
      (2 ^ Fintype.card Feature) := by
  classical
  refine
    ⟨Finset.univ.image (fun h : Feature → Bool => fun x : Input => h (featureOf x)),
      ?_, ?_⟩
  · intro h
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
  · exact le_trans Finset.card_image_le (by simp)

/-- Arbitrary feature readout realizes every Boolean rule on the input exactly
when the feature map is injective. -/
theorem featureReadoutFamily_surjective_predict_iff_injective
    (featureOf : Input → Feature) :
    Function.Surjective (featureReadoutFamily featureOf).predict ↔
      Function.Injective featureOf := by
  constructor
  · intro hsurj x y hfeature
    classical
    by_contra hne
    let target : Input → Bool := fun z => if z = x then true else false
    rcases hsurj target with ⟨h, hh⟩
    have hx : h (featureOf x) = true := by
      have hpoint := congrFun hh x
      simpa [featureReadoutFamily, target] using hpoint
    have hy : h (featureOf y) = false := by
      have hpoint := congrFun hh y
      have hyx : y ≠ x := fun hyx => hne hyx.symm
      simpa [featureReadoutFamily, target, hyx] using hpoint
    rw [hfeature] at hx
    exact Bool.noConfusion (hx.symm.trans hy)
  · intro hinj target
    classical
    refine
      ⟨fun feature =>
          if h : ∃ x, featureOf x = feature then target (Classical.choose h) else false,
        ?_⟩
    funext x
    have hx : ∃ y, featureOf y = featureOf x := ⟨x, rfl⟩
    have hchoose : Classical.choose hx = x :=
      hinj (Classical.choose_spec hx)
    simp [featureReadoutFamily, hx, hchoose]

/-- Any feature route that realizes all full rules must have at least as many
feature values as input points. -/
theorem featureReadoutFamily_surfaceCard_le_featureCard_of_surjective
    [Fintype Input] [Fintype Feature] (featureOf : Input → Feature)
    (hsurj : Function.Surjective (featureReadoutFamily featureOf).predict) :
    Fintype.card Input ≤ Fintype.card Feature := by
  exact
    Fintype.card_le_of_injective featureOf
      ((featureReadoutFamily_surjective_predict_iff_injective featureOf).1 hsurj)

/-- A full-rule feature route inherits the full Boolean classifier-space lower
bound for every finite predictor-image cover. -/
theorem featureReadoutFamily_cover_floor_of_surjective
    [Fintype Input] (featureOf : Input → Feature) {N : ℕ}
    (hsurj : Function.Surjective (featureReadoutFamily featureOf).predict)
    (hcover : (featureReadoutFamily featureOf).FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
      (G := featureReadoutFamily featureOf) hsurj hcover

/-- Cardinally small feature spaces cannot realize the full Boolean rule
family on the input. -/
theorem not_featureReadoutFamily_surjective_of_featureCard_lt_surfaceCard
    [Fintype Input] [Fintype Feature] (featureOf : Input → Feature)
    (hcard : Fintype.card Feature < Fintype.card Input) :
    ¬ Function.Surjective (featureReadoutFamily featureOf).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hcard
    (featureReadoutFamily_surfaceCard_le_featureCard_of_surjective
      featureOf hsurj)

end FeatureReadout

section ExactVisibleFeatureRoute

variable {Z : Type u} [Fintype Z] {Feature : Type v} [Fintype Feature]
variable {k N : ℕ}

/-- Exact-visible specialization: full-rule feature repair forces both the
surface-cardinality floor and the full Boolean image floor. -/
theorem exactVisibleFeatureRoute_fullRuleRepair_forces_floors
    (featureOf : ExactVisiblePostSwitchSurface Z k → Feature)
    (hsurj : Function.Surjective (featureReadoutFamily featureOf).predict)
    (hcover : (featureReadoutFamily featureOf).FinitePredictorCover N) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Feature ∧
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    ⟨featureReadoutFamily_surfaceCard_le_featureCard_of_surjective
        featureOf hsurj,
      featureReadoutFamily_cover_floor_of_surjective featureOf hsurj hcover⟩

/-- Exact-visible specialization: below the surface-cardinality floor, no
feature encoding can realize every full rule, even though its feature image is
finite. -/
theorem exactVisibleFeatureRoute_cardinality_obstruction_packet
    (featureOf : ExactVisiblePostSwitchSurface Z k → Feature)
    (hcard :
      Fintype.card Feature < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (featureReadoutFamily featureOf).FinitePredictorCover
        (2 ^ Fintype.card Feature) ∧
      ¬ Function.Surjective (featureReadoutFamily featureOf).predict := by
  exact
    ⟨featureReadoutFamily_finitePredictorCover_card featureOf,
      not_featureReadoutFamily_surjective_of_featureCard_lt_surfaceCard
        featureOf hcard⟩

end ExactVisibleFeatureRoute

section QuantaleFeatureBoundary

variable {α : Type u} [Fintype α] {Feature : Type v}

/-- A feature map resolves the supported involution pairs when it separates at
least one positive-weight pair. -/
def FeatureResolvesPositivePair
    (τ : α → α) (featureOf : α → Feature) (w : α → ℕ) : Prop :=
  ∃ x, 0 < w x ∧ featureOf (τ x) ≠ featureOf x

/-- If the feature is supportwise invariant across a target-flipping involution,
no classifier on that feature has positive doubled advantage. -/
theorem not_pos_doubledAdvantage_of_supportwise_feature_invariant
    (τ : α → α) (featureOf : α → Feature)
    (y : α → Bool) (w : α → ℕ) (h : Feature → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hfeature : ∀ x, 0 < w x → featureOf (τ x) = featureOf x) :
    ¬ 0 < doubledAdvantage featureOf y w h := by
  exact
    not_pos_doubledAdvantage_of_supportwise_prediction_invariant
      τ featureOf y w h hτ hy hw
      (by
        intro x hx
        rw [hfeature x hx])

/-- The same supportwise feature invariance blocks strict half-accuracy
advantage. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_supportwise_feature_invariant
    (τ : α → α) (featureOf : α → Feature)
    (y : α → Bool) (w : α → ℕ) (h : Feature → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hfeature : ∀ x, 0 < w x → featureOf (τ x) = featureOf x) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass featureOf y w h := by
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      τ featureOf y w h hτ hy hw
      (by
        intro x hx
        rw [hfeature x hx])

/-- Any positive doubled-advantage classifier on a feature must separate some
positive-weight involution pair. -/
theorem featureResolvesPositivePair_of_pos_doubledAdvantage
    (τ : α → α) (featureOf : α → Feature)
    (y : α → Bool) (w : α → ℕ) (h : Feature → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage featureOf y w h) :
    FeatureResolvesPositivePair τ featureOf w := by
  rcases
    exists_positive_prediction_ne_of_pos_doubledAdvantage
      τ featureOf y w h hτ hy hw hadv with
    ⟨x, hxw, hpred⟩
  refine ⟨x, hxw, ?_⟩
  intro hfeature
  exact hpred (by rw [hfeature])

/-- Strict half-accuracy advantage also forces the feature to separate some
positive-weight involution pair. -/
theorem featureResolvesPositivePair_of_total_lt_two_mul_weightedCorrectMass
    (τ : α → α) (featureOf : α → Feature)
    (y : α → Bool) (w : α → ℕ) (h : Feature → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass featureOf y w h) :
    FeatureResolvesPositivePair τ featureOf w := by
  rcases
    exists_positive_prediction_ne_of_total_lt_two_mul_weightedCorrectMass
      τ featureOf y w h hτ hy hw hadv with
    ⟨x, hxw, hpred⟩
  refine ⟨x, hxw, ?_⟩
  intro hfeature
  exact hpred (by rw [hfeature])

end QuantaleFeatureBoundary

/-- Combined boundary: an arbitrary feature-map repair of the Kpoly full-rule
route must pay the exact-visible surface and Boolean-image floors, while any
weakness advantage through a feature must resolve a positive-weight involution
pair. -/
theorem kpolyFeatureRouteQuantale_shortcutRemoval_boundary_packet
    {Z : Type u} [Fintype Z] {SurfaceFeature : Type v} [Fintype SurfaceFeature]
    {k N : ℕ}
    (surfaceFeature : ExactVisiblePostSwitchSurface Z k → SurfaceFeature)
    (hsurj : Function.Surjective (featureReadoutFamily surfaceFeature).predict)
    (hcover : (featureReadoutFamily surfaceFeature).FinitePredictorCover N)
    {α : Type w} [Fintype α] {WeakFeature : Type v}
    (τ : α → α) (weakFeature : α → WeakFeature)
    (y : α → Bool) (wgt : α → ℕ) (h : WeakFeature → Bool)
    (hτ : Function.Involutive τ)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, wgt (τ x) = wgt x) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        Fintype.card SurfaceFeature ∧
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N ∧
      (∀ _ : ∀ x, 0 < wgt x → weakFeature (τ x) = weakFeature x,
        (¬ 0 < doubledAdvantage weakFeature y wgt h) ∧
          ¬ weightedTotalMass wgt < 2 * weightedCorrectMass weakFeature y wgt h) ∧
      (0 < doubledAdvantage weakFeature y wgt h →
        FeatureResolvesPositivePair τ weakFeature wgt) ∧
      (weightedTotalMass wgt < 2 * weightedCorrectMass weakFeature y wgt h →
        FeatureResolvesPositivePair τ weakFeature wgt) := by
  refine
    ⟨(exactVisibleFeatureRoute_fullRuleRepair_forces_floors
        surfaceFeature hsurj hcover).1,
      (exactVisibleFeatureRoute_fullRuleRepair_forces_floors
        surfaceFeature hsurj hcover).2,
      ?_, ?_, ?_⟩
  · intro hfeature
    exact
      ⟨not_pos_doubledAdvantage_of_supportwise_feature_invariant
          τ weakFeature y wgt h hτ hy hw hfeature,
        not_total_lt_two_mul_weightedCorrectMass_of_supportwise_feature_invariant
          τ weakFeature y wgt h hτ hy hw hfeature⟩
  · intro hadv
    exact
      featureResolvesPositivePair_of_pos_doubledAdvantage
        τ weakFeature y wgt h hτ hy hw hadv
  · intro hadv
    exact
      featureResolvesPositivePair_of_total_lt_two_mul_weightedCorrectMass
        τ weakFeature y wgt h hτ hy hw hadv

end Mettapedia.Computability.PNP
