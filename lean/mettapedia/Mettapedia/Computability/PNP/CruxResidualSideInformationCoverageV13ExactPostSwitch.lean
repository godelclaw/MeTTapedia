import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchActiveOrbit
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchSupportedBudget
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchFork

/-!
# PNP residual-side-information V13 exact post-switch subcoverage

This module packages the exact post-switch active-orbit part of the V13
residual-side-information subledger.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The V13 exact post-switch layer: the active orbit realizes the pure residual
package, the prediction witness, and the fork-obstruction package. -/
def V13ResidualSideInformationExactPostSwitchSubcoverage : Prop :=
  (∀ {Z : Type u} [Fintype Z] (z0 : Z),
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
  (∀ {Z : Type u} [Fintype Z] (z0 : Z),
      (∀ u : ExactVisiblePostSwitchSurface Z 1,
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
  (∀ {Z : Type u} [Fintype Z] (z0 : Z),
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

@[simp] theorem v13ResidualSideInformationExactPostSwitchSubcoverage :
    V13ResidualSideInformationExactPostSwitchSubcoverage := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
        (Z := Z) z0
  · intro Z _FintypeZ z0
    exact
      residualSideInformationCoverage_anchor_exactPostSwitch_prediction_witness_forces_fork_obstruction
        (Z := Z) z0

end Mettapedia.Computability.PNP
