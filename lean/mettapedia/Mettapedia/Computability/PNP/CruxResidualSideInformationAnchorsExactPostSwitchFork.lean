import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchSupportedBudget

/-!
# PNP residual-side-information anchors: exact post-switch fork obstruction

This module connects the active-orbit prediction witness to the fork-obstruction
package on the exact visible post-switch surface.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active-orbit residual prediction witness already carries
the fork-obstruction package on the same two-point orbit.  So classifier-level
residual prediction separation is not a fresh concrete route on that surface:
it already brings strict half-accuracy success, positive nonzero-column mass,
and failure of exact-input-invariant support. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_prediction_witness_forces_fork_obstruction
    {Z : Type*} [Fintype Z] (z0 : Z) :
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
      ¬ exactInputInvariantWeightedSupport (activeOrbitWeight z0) := by
  exact ⟨
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
      (Z := Z) z0,
    exactPostSwitch_activeOrbit_forces_fork_obstruction (Z := Z) z0
  ⟩

end Mettapedia.Computability.PNP
