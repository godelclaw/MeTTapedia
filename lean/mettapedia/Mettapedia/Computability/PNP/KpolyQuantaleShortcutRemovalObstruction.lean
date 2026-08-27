import Mettapedia.Computability.PNP.KpolyFeatureRouteQuantaleBoundary
import Mettapedia.Computability.PNP.KpolySupportSurjectivityQuantaleObstruction

/-!
# Kpoly and quantale route-class obstruction after shortcut removal

This module packages the feature-map Kpoly boundary, the observed-support
boundary, and the quantale weakness boundary into one route-class statement.
Small polynomial or feature image evidence is not enough: a route that clears
this class must pay the exact-visible feature floor, recover every support point,
and resolve a positive-weight weakness pair.

No final complexity-class separation is asserted here.
-/

namespace Mettapedia.Computability.PNP

universe u v w x y

/-- A shortcut-removed Kpoly/quantale route attempt.  It combines the three
obligations that remain after the polynomial-image shortcut has been removed:
full-rule feature repair, exact observed-support point queries, and a positive
feature-based weakness advantage. -/
structure KpolyQuantaleShortcutRemovalRoute
    {Z : Type u} [Fintype Z]
    {SurfaceFeature : Type v} [Fintype SurfaceFeature]
    {Block : Type w}
    (k N : ℕ)
    (surfaceFeature : ExactVisiblePostSwitchSurface Z k → SurfaceFeature)
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type x} [Fintype α] {WeakFeature : Type y}
    (τ : α → α) (weakFeature : α → WeakFeature)
    (target : α → Bool) (weight : α → ℕ) (classifier : WeakFeature → Bool) :
    Prop where
  fullRuleFeatureRepair :
    Function.Surjective (featureReadoutFamily surfaceFeature).predict
  finiteFeatureCover :
    (featureReadoutFamily surfaceFeature).FinitePredictorCover N
  allSupportPointQueries :
    ∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
                rule) =
            rule u₀
  positiveWeaknessAdvantage :
    0 < doubledAdvantage weakFeature target weight classifier

/-- Any route in this shortcut-removed class must pay the exact-visible feature
floor and Boolean image floor, make the support/query map surjective, and resolve
a positive-weight weakness pair. -/
theorem kpolyQuantaleShortcutRemovalRoute_necessary_obligations
    {Z : Type u} [Fintype Z]
    {SurfaceFeature : Type v} [Fintype SurfaceFeature]
    {Block : Type w} {k N : ℕ}
    {surfaceFeature : ExactVisiblePostSwitchSurface Z k → SurfaceFeature}
    {visibleOf : Block → ExactVisiblePostSwitchSurface Z k}
    {α : Type x} [Fintype α] {WeakFeature : Type y}
    {τ : α → α} {weakFeature : α → WeakFeature}
    {target : α → Bool} {weight : α → ℕ} {classifier : WeakFeature → Bool}
    (hτ : Function.Involutive τ)
    (htarget : ∀ x, target (τ x) = !(target x))
    (hweight : ∀ x, weight (τ x) = weight x)
    (route :
      KpolyQuantaleShortcutRemovalRoute
        k N surfaceFeature visibleOf τ weakFeature target weight classifier) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
        Fintype.card SurfaceFeature ∧
      2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N ∧
      Function.Surjective visibleOf ∧
      FeatureResolvesPositivePair τ weakFeature weight := by
  have hfloors :=
    exactVisibleFeatureRoute_fullRuleRepair_forces_floors
      surfaceFeature route.fullRuleFeatureRepair route.finiteFeatureCover
  have hsupport :
      Function.Surjective visibleOf :=
    (supportFullRule_all_evalDecoders_iff_visibleOf_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf).1
      route.allSupportPointQueries
  have hweak :
      FeatureResolvesPositivePair τ weakFeature weight :=
    featureResolvesPositivePair_of_pos_doubledAdvantage
      τ weakFeature target weight classifier hτ htarget hweight
      route.positiveWeaknessAdvantage
  exact ⟨hfloors.1, hfloors.2, hsupport, hweak⟩

/-- Missing any one of the shortcut-removed route obligations blocks the whole
route class: below-surface feature space, non-surjective support/query map, or
supportwise-invariant weakness feature. -/
theorem not_kpolyQuantaleShortcutRemovalRoute_of_missing_obligation
    {Z : Type u} [Fintype Z]
    {SurfaceFeature : Type v} [Fintype SurfaceFeature]
    {Block : Type w} {k N : ℕ}
    {surfaceFeature : ExactVisiblePostSwitchSurface Z k → SurfaceFeature}
    {visibleOf : Block → ExactVisiblePostSwitchSurface Z k}
    {α : Type x} [Fintype α] {WeakFeature : Type y}
    {τ : α → α} {weakFeature : α → WeakFeature}
    {target : α → Bool} {weight : α → ℕ} {classifier : WeakFeature → Bool}
    (hτ : Function.Involutive τ)
    (htarget : ∀ x, target (τ x) = !(target x))
    (hweight : ∀ x, weight (τ x) = weight x)
    (hblocked :
      Fintype.card SurfaceFeature <
          Fintype.card (ExactVisiblePostSwitchSurface Z k) ∨
        ¬ Function.Surjective visibleOf ∨
        (∀ x, 0 < weight x → weakFeature (τ x) = weakFeature x)) :
    ¬ KpolyQuantaleShortcutRemovalRoute
        k N surfaceFeature visibleOf τ weakFeature target weight classifier := by
  intro route
  rcases hblocked with hsmall | hnonsurj | hinvariant
  · have hobligations :=
      kpolyQuantaleShortcutRemovalRoute_necessary_obligations
        (surfaceFeature := surfaceFeature) (visibleOf := visibleOf)
        (τ := τ) (weakFeature := weakFeature) (target := target)
        (weight := weight) (classifier := classifier)
        hτ htarget hweight route
    exact Nat.not_le_of_lt hsmall hobligations.1
  · have hobligations :=
      kpolyQuantaleShortcutRemovalRoute_necessary_obligations
        (surfaceFeature := surfaceFeature) (visibleOf := visibleOf)
        (τ := τ) (weakFeature := weakFeature) (target := target)
        (weight := weight) (classifier := classifier)
        hτ htarget hweight route
    exact hnonsurj hobligations.2.2.1
  · exact
      not_pos_doubledAdvantage_of_supportwise_feature_invariant
        τ weakFeature target weight classifier hτ htarget hweight hinvariant
        route.positiveWeaknessAdvantage

/-- Public packet for the shortcut-removed route class: route clearance implies
all three central obligations, and any explicit missing obligation blocks the
class. -/
theorem kpolyQuantaleShortcutRemoval_obstruction_packet
    {Z : Type u} [Fintype Z]
    {SurfaceFeature : Type v} [Fintype SurfaceFeature]
    {Block : Type w} {k N : ℕ}
    {surfaceFeature : ExactVisiblePostSwitchSurface Z k → SurfaceFeature}
    {visibleOf : Block → ExactVisiblePostSwitchSurface Z k}
    {α : Type x} [Fintype α] {WeakFeature : Type y}
    {τ : α → α} {weakFeature : α → WeakFeature}
    {target : α → Bool} {weight : α → ℕ} {classifier : WeakFeature → Bool}
    (hτ : Function.Involutive τ)
    (htarget : ∀ x, target (τ x) = !(target x))
    (hweight : ∀ x, weight (τ x) = weight x)
    (hblocked :
      Fintype.card SurfaceFeature <
          Fintype.card (ExactVisiblePostSwitchSurface Z k) ∨
        ¬ Function.Surjective visibleOf ∨
        (∀ x, 0 < weight x → weakFeature (τ x) = weakFeature x)) :
    (∀ _ :
      KpolyQuantaleShortcutRemovalRoute
        k N surfaceFeature visibleOf τ weakFeature target weight classifier,
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
          Fintype.card SurfaceFeature ∧
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N ∧
        Function.Surjective visibleOf ∧
        FeatureResolvesPositivePair τ weakFeature weight) ∧
      ¬ KpolyQuantaleShortcutRemovalRoute
          k N surfaceFeature visibleOf τ weakFeature target weight classifier := by
  exact
    ⟨fun route =>
        kpolyQuantaleShortcutRemovalRoute_necessary_obligations
          (surfaceFeature := surfaceFeature) (visibleOf := visibleOf)
          (τ := τ) (weakFeature := weakFeature) (target := target)
          (weight := weight) (classifier := classifier)
          hτ htarget hweight route,
      not_kpolyQuantaleShortcutRemovalRoute_of_missing_obligation
        (surfaceFeature := surfaceFeature) (visibleOf := visibleOf)
        (τ := τ) (weakFeature := weakFeature) (target := target)
        (weight := weight) (classifier := classifier)
        hτ htarget hweight hblocked⟩

end Mettapedia.Computability.PNP
