import Mettapedia.Computability.PNP.KpolyQuantaleShortcutRemovalCanary

/-!
# Regression checks for the shortcut-removal route canary

These checks keep the route-class inhabitance proof from silently disappearing.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

noncomputable section

theorem kpolyQuantaleShortcutRemovalRoute_nonempty_regression :
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
  exact kpolyQuantaleShortcutRemovalRoute_nonempty

theorem kpolyQuantaleShortcutRemoval_positive_canary_packet_regression :
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
  exact kpolyQuantaleShortcutRemoval_positive_canary_packet

theorem kpolyQuantaleShortcutRemoval_positive_canary_necessary_obligations_regression :
    Fintype.card KpolyShortcutCanarySurface ≤
        Fintype.card KpolyShortcutCanaryFeature ∧
      2 ^ Fintype.card KpolyShortcutCanarySurface ≤ 2 ∧
      Function.Surjective kpolyShortcutCanaryVisibleOf ∧
      FeatureResolvesPositivePair
        kpolyShortcutCanaryTau
        kpolyShortcutCanaryWeakFeature
        kpolyShortcutCanaryWeight := by
  exact kpolyQuantaleShortcutRemoval_positive_canary_necessary_obligations

end

end Mettapedia.Computability.PNP
