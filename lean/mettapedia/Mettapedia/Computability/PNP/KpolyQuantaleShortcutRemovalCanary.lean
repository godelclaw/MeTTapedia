import Mettapedia.Computability.PNP.KpolyQuantaleShortcutRemovalObstruction
import Mathlib.Tactic

/-!
# Positive canary for the Kpoly/quantale shortcut-removal route class

This module resolves the route-class vacuity check for
`KpolyQuantaleShortcutRemovalRoute`: the class is inhabited by a concrete
singleton exact-visible surface and a two-point weakness orbit.

The canary is deliberately small.  It proves that the obstruction packet is a
non-vacuous necessary-condition theorem for this route class, not a P versus NP
claim and not a meaningful scaled route.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

noncomputable section

/-- The singleton exact-visible surface: `Z = Unit`, `k = 0`. -/
abbrev KpolyShortcutCanarySurface :=
  ExactVisiblePostSwitchSurface Unit 0

/-- The canary feature type is the exact-visible surface itself. -/
abbrev KpolyShortcutCanaryFeature :=
  KpolyShortcutCanarySurface

/-- The canary block type is the exact-visible surface itself. -/
abbrev KpolyShortcutCanaryBlock :=
  KpolyShortcutCanarySurface

/-- Two-point weakness orbit for the canary. -/
abbrev KpolyShortcutCanaryAlpha :=
  Bool

/-- Weakness feature type for the canary. -/
abbrev KpolyShortcutCanaryWeakFeature :=
  Bool

/-- The unique exact-visible canary point. -/
def kpolyShortcutCanaryPoint : KpolyShortcutCanarySurface :=
  ⟨(), zeroVec, zeroVec⟩

/-- Identity surface feature map. -/
def kpolyShortcutCanarySurfaceFeature :
    KpolyShortcutCanarySurface → KpolyShortcutCanaryFeature :=
  id

/-- Identity observed-support map. -/
def kpolyShortcutCanaryVisibleOf :
    KpolyShortcutCanaryBlock → KpolyShortcutCanarySurface :=
  id

/-- The two-point target-flipping involution. -/
def kpolyShortcutCanaryTau :
    KpolyShortcutCanaryAlpha → KpolyShortcutCanaryAlpha :=
  fun x => !x

/-- Identity weakness feature. -/
def kpolyShortcutCanaryWeakFeature :
    KpolyShortcutCanaryAlpha → KpolyShortcutCanaryWeakFeature :=
  id

/-- Identity target on the two-point weakness orbit. -/
def kpolyShortcutCanaryTarget :
    KpolyShortcutCanaryAlpha → Bool :=
  id

/-- Unit positive weights on both weakness points. -/
def kpolyShortcutCanaryWeight :
    KpolyShortcutCanaryAlpha → ℕ :=
  fun _ => 1

/-- Identity classifier, perfectly correct on the two-point weakness orbit. -/
def kpolyShortcutCanaryClassifier :
    KpolyShortcutCanaryWeakFeature → Bool :=
  id

theorem kpolyShortcutCanarySurface_subsingleton :
    Subsingleton KpolyShortcutCanarySurface := by
  constructor
  intro u v
  cases u with
  | mk z1 a1 b1 =>
      cases v with
      | mk z2 a2 b2 =>
          cases z1
          cases z2
          have ha : a1 = a2 := by
            funext i
            exact nomatch i
          have hb : b1 = b2 := by
            funext i
            exact nomatch i
          cases ha
          cases hb
          rfl

theorem kpolyShortcutCanarySurface_card :
    Fintype.card KpolyShortcutCanarySurface = 1 := by
  letI : Subsingleton KpolyShortcutCanarySurface :=
    kpolyShortcutCanarySurface_subsingleton
  exact Fintype.card_ofSubsingleton kpolyShortcutCanaryPoint

theorem kpolyShortcutCanaryFeature_truthTableBudget_eq_two :
    2 ^ Fintype.card KpolyShortcutCanaryFeature = 2 := by
  rw [kpolyShortcutCanarySurface_card]
  norm_num

theorem kpolyShortcutCanary_fullRuleFeatureRepair :
    Function.Surjective
      (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).predict := by
  exact
    (featureReadoutFamily_surjective_predict_iff_injective
      kpolyShortcutCanarySurfaceFeature).2 (fun _ _ h => h)

theorem kpolyShortcutCanary_finiteFeatureCover :
    (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).FinitePredictorCover
      2 := by
  have hcover :=
    featureReadoutFamily_finitePredictorCover_card
      kpolyShortcutCanarySurfaceFeature
  simpa [kpolyShortcutCanaryFeature_truthTableBudget_eq_two] using hcover

theorem kpolyShortcutCanary_allSupportPointQueries :
    ∀ u₀ : KpolyShortcutCanarySurface,
      ∃ decode : (KpolyShortcutCanaryBlock → Bool) → Bool,
        ∀ rule : ExactVisibleRule Unit 0,
          decode
              ((supportFullRuleActualSwitchedLocalInterface
                kpolyShortcutCanaryVisibleOf).outputFamily.predict rule) =
            rule u₀ := by
  exact
    (supportFullRule_all_evalDecoders_iff_visibleOf_surjective
      kpolyShortcutCanaryVisibleOf).2 (fun u => ⟨u, rfl⟩)

theorem kpolyShortcutCanary_positiveWeaknessAdvantage :
    0 <
      doubledAdvantage
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryTarget
        kpolyShortcutCanaryWeight
        kpolyShortcutCanaryClassifier := by
  norm_num [doubledAdvantage, weightedCorrectMass, weightedTotalMass,
    kpolyShortcutCanaryWeakFeature, kpolyShortcutCanaryTarget,
    kpolyShortcutCanaryWeight, kpolyShortcutCanaryClassifier, Correct]

theorem kpolyShortcutCanaryTau_involutive :
    Function.Involutive kpolyShortcutCanaryTau := by
  intro x
  cases x <;> rfl

theorem kpolyShortcutCanaryTarget_flips :
    ∀ x, kpolyShortcutCanaryTarget (kpolyShortcutCanaryTau x) =
      !(kpolyShortcutCanaryTarget x) := by
  intro x
  cases x <;> rfl

theorem kpolyShortcutCanaryWeight_preserved :
    ∀ x, kpolyShortcutCanaryWeight (kpolyShortcutCanaryTau x) =
      kpolyShortcutCanaryWeight x := by
  intro x
  rfl

/-- The concrete inhabited shortcut-removal route. -/
def kpolyQuantaleShortcutRemovalPositiveRoute :
    KpolyQuantaleShortcutRemovalRoute
      0 2
      kpolyShortcutCanarySurfaceFeature
      kpolyShortcutCanaryVisibleOf
      kpolyShortcutCanaryTau
      kpolyShortcutCanaryWeakFeature
      kpolyShortcutCanaryTarget
      kpolyShortcutCanaryWeight
      kpolyShortcutCanaryClassifier where
  fullRuleFeatureRepair := kpolyShortcutCanary_fullRuleFeatureRepair
  finiteFeatureCover := kpolyShortcutCanary_finiteFeatureCover
  allSupportPointQueries := kpolyShortcutCanary_allSupportPointQueries
  positiveWeaknessAdvantage := kpolyShortcutCanary_positiveWeaknessAdvantage

/-- A committed positive canary package for the route-class inhabitance check. -/
structure KpolyQuantaleShortcutRemovalPositiveCanary where
  route :
    KpolyQuantaleShortcutRemovalRoute
      0 2
      kpolyShortcutCanarySurfaceFeature
      kpolyShortcutCanaryVisibleOf
      kpolyShortcutCanaryTau
      kpolyShortcutCanaryWeakFeature
      kpolyShortcutCanaryTarget
      kpolyShortcutCanaryWeight
      kpolyShortcutCanaryClassifier
  surfaceCardOne :
    Fintype.card KpolyShortcutCanarySurface = 1
  truthTableBudgetTwo :
    2 ^ Fintype.card KpolyShortcutCanaryFeature = 2
  fullRuleFeatureRepair :
    Function.Surjective
      (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).predict
  finiteFeatureCover :
    (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).FinitePredictorCover
      2
  allSupportPointQueries :
    ∀ u₀ : KpolyShortcutCanarySurface,
      ∃ decode : (KpolyShortcutCanaryBlock → Bool) → Bool,
        ∀ rule : ExactVisibleRule Unit 0,
          decode
              ((supportFullRuleActualSwitchedLocalInterface
                kpolyShortcutCanaryVisibleOf).outputFamily.predict rule) =
            rule u₀
  positiveWeaknessAdvantage :
    0 <
      doubledAdvantage
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryTarget
        kpolyShortcutCanaryWeight
        kpolyShortcutCanaryClassifier

/-- The concrete positive canary term. -/
def kpolyQuantaleShortcutRemovalPositiveCanary :
    KpolyQuantaleShortcutRemovalPositiveCanary where
  route := kpolyQuantaleShortcutRemovalPositiveRoute
  surfaceCardOne := kpolyShortcutCanarySurface_card
  truthTableBudgetTwo := kpolyShortcutCanaryFeature_truthTableBudget_eq_two
  fullRuleFeatureRepair := kpolyShortcutCanary_fullRuleFeatureRepair
  finiteFeatureCover := kpolyShortcutCanary_finiteFeatureCover
  allSupportPointQueries := kpolyShortcutCanary_allSupportPointQueries
  positiveWeaknessAdvantage := kpolyShortcutCanary_positiveWeaknessAdvantage

/-- The audited route class is inhabited; the obstruction packet is therefore
not vacuous on its own type signature. -/
theorem kpolyQuantaleShortcutRemovalRoute_nonempty :
    Nonempty
      (KpolyQuantaleShortcutRemovalRoute
        0 2
        kpolyShortcutCanarySurfaceFeature
        kpolyShortcutCanaryVisibleOf
        kpolyShortcutCanaryTau
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryTarget
        kpolyShortcutCanaryWeight
        kpolyShortcutCanaryClassifier) := by
  exact ⟨kpolyQuantaleShortcutRemovalPositiveRoute⟩

/-- The positive canary exposes all four route obligations directly. -/
theorem kpolyQuantaleShortcutRemoval_positive_canary_packet :
    Nonempty
      (KpolyQuantaleShortcutRemovalRoute
        0 2
        kpolyShortcutCanarySurfaceFeature
        kpolyShortcutCanaryVisibleOf
        kpolyShortcutCanaryTau
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryTarget
        kpolyShortcutCanaryWeight
        kpolyShortcutCanaryClassifier) ∧
      Function.Surjective
        (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).predict ∧
      (featureReadoutFamily kpolyShortcutCanarySurfaceFeature).FinitePredictorCover
        2 ∧
      (∀ u₀ : KpolyShortcutCanarySurface,
        ∃ decode : (KpolyShortcutCanaryBlock → Bool) → Bool,
          ∀ rule : ExactVisibleRule Unit 0,
            decode
                ((supportFullRuleActualSwitchedLocalInterface
                  kpolyShortcutCanaryVisibleOf).outputFamily.predict rule) =
              rule u₀) ∧
      0 <
        doubledAdvantage
          kpolyShortcutCanaryWeakFeature
          kpolyShortcutCanaryTarget
          kpolyShortcutCanaryWeight
          kpolyShortcutCanaryClassifier := by
  exact
    ⟨kpolyQuantaleShortcutRemovalRoute_nonempty,
      kpolyShortcutCanary_fullRuleFeatureRepair,
      kpolyShortcutCanary_finiteFeatureCover,
      kpolyShortcutCanary_allSupportPointQueries,
      kpolyShortcutCanary_positiveWeaknessAdvantage⟩

/-- The existing necessary-obligations theorem fires on the positive canary. -/
theorem kpolyQuantaleShortcutRemoval_positive_canary_necessary_obligations :
    Fintype.card KpolyShortcutCanarySurface ≤
        Fintype.card KpolyShortcutCanaryFeature ∧
      2 ^ Fintype.card KpolyShortcutCanarySurface ≤ 2 ∧
      Function.Surjective kpolyShortcutCanaryVisibleOf ∧
      FeatureResolvesPositivePair
        kpolyShortcutCanaryTau
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryWeight := by
  exact
    kpolyQuantaleShortcutRemovalRoute_necessary_obligations
      (surfaceFeature := kpolyShortcutCanarySurfaceFeature)
      (visibleOf := kpolyShortcutCanaryVisibleOf)
      (τ := kpolyShortcutCanaryTau)
      (weakFeature := kpolyShortcutCanaryWeakFeature)
      (target := kpolyShortcutCanaryTarget)
      (weight := kpolyShortcutCanaryWeight)
      (classifier := kpolyShortcutCanaryClassifier)
      kpolyShortcutCanaryTau_involutive
      kpolyShortcutCanaryTarget_flips
      kpolyShortcutCanaryWeight_preserved
      kpolyQuantaleShortcutRemovalPositiveRoute

end

end Mettapedia.Computability.PNP
