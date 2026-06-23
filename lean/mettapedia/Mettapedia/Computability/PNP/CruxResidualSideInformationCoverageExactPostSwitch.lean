import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchActiveOrbit
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchSupportedBudget
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchFork

/-!
# PNP residual-side-information exact post-switch coverage

This module packages the exact post-switch active-orbit part of broad
residual-side-information coverage.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The broad residual-side-information exact post-switch layer: the
manuscript's active orbit carries the pure residual package, the supported
obstruction package with no visible-pair balancing, and the fork-obstruction
package. -/
def ResidualSideInformationExactPostSwitchCoverage : Prop :=
  (∀ {Z : Type} [Fintype Z] (z0 : Z),
      0 < resolvedMass tiInputMap
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0) ∧
        ¬ SideInfoDeterminedBy invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
        PositiveWeightSideInfoCollisionOverBase invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
            (tiInputMap u).b ≠ u.b) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
              (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b))) ∧
  (∀ {Z : Type} [Fintype Z] (z0 : Z),
      0 <
        doubledAdvantage
          activeOrbitFeatures
          activeOrbitTarget
          (activeOrbitWeight z0)
          activeOrbitClassifier ∧
        0 < resolvedMass tiInputMap
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          (activeOrbitWeight z0) ∧
        ¬ SideInfoDeterminedBy invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) ∧
        ¬ SupportwiseSourceOnlyPairClassifier
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
            (activeOrbitWeight z0)
            activeOrbitClassifier ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            invariantVisibleData (tiInputMap u) = invariantVisibleData u ∧
            (tiInputMap u).b ≠ u.b) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            ¬ SourceOnlyPredicateCapturesSideEq invariantVisibleData
              (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
              activeOrbitClassifier (activeOrbitFeatures u)) ∧
        ¬ SupportwiseVisiblePairBalancing
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
            activeOrbitTarget
            (activeOrbitWeight z0)) ∧
  (∀ {Z : Type} [Fintype Z] (z0 : Z),
      ((∀ u : ExactVisiblePostSwitchSurface Z 1,
          invariantVisibleData (tiInputMap u) = invariantVisibleData u) ∧
        (∀ u : ExactVisiblePostSwitchSurface Z 1,
          activeOrbitWeight z0 (tiInputMap u) = activeOrbitWeight z0 u) ∧
        (∀ u : ExactVisiblePostSwitchSurface Z 1, 0 < activeOrbitWeight z0 u →
          activeOrbitTarget (tiInputMap u) = !(activeOrbitTarget u)) ∧
        0 <
          doubledAdvantage
            activeOrbitFeatures
            activeOrbitTarget
            (activeOrbitWeight z0)
            activeOrbitClassifier ∧
        (∃ u : ExactVisiblePostSwitchSurface Z 1,
          0 < activeOrbitWeight z0 u ∧
            activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
              activeOrbitClassifier (activeOrbitFeatures u))) ∧
        weightedTotalMass (activeOrbitWeight z0) <
          2 * weightedCorrectMass
            activeOrbitFeatures
            activeOrbitTarget
            (activeOrbitWeight z0)
            activeOrbitClassifier ∧
        0 <
          sliceMass
            (fun u : ExactVisiblePostSwitchSurface Z 1 => nonzeroColumn u.a)
            (activeOrbitWeight z0) ∧
        ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0))

@[simp] theorem residualSideInformationExactPostSwitchCoverage :
    ResidualSideInformationExactPostSwitchCoverage := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_supported_obstruction_package_and_no_visible_pair_balancing
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_prediction_witness_forces_fork_obstruction
        (Z := Z) z0

end Mettapedia.Computability.PNP
