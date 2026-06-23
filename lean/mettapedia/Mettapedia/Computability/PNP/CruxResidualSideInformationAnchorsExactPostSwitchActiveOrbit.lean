import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess
import Mettapedia.Computability.PNP.PostSwitchResidualWitnessCore
import Mettapedia.Computability.PNP.PostSwitchResidualWitnessSupport
import Mettapedia.Computability.PNP.PostSwitchResidualWitnessAdvantage
import Mettapedia.Computability.PNP.PostSwitchResidualWitnessPackages

/-!
# PNP residual-side-information anchors: exact post-switch active orbit

This module records the concrete active-orbit pure residual package and
prediction witness on the exact visible post-switch surface.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit already realizes positive
resolved mass together with the pure residual obstruction package, before any
classifier-level prediction-separation argument is invoked. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
    {Z : Type*} [Fintype Z] (z0 : Z) :
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
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) := by
  exact
    exactPostSwitch_activeOrbit_realizes_pure_residual_obstruction_package
      (Z := Z) z0

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit already realizes the
classifier-level residual prediction witness as well.  The invariant
projection is preserved, the active weight is involution-symmetric, the target
flips on positive support, the concrete classifier has positive doubled
advantage, and some positive-weight involution pair is separated by the final
classifier output. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
    {Z : Type*} [Fintype Z] (z0 : Z) :
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
    ∃ u : ExactVisiblePostSwitchSurface Z 1,
      0 < activeOrbitWeight z0 u ∧
      activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
        activeOrbitClassifier (activeOrbitFeatures u) := by
  exact
    exactPostSwitch_activeOrbit_realizes_residual_prediction_witness
      (Z := Z) z0

end Mettapedia.Computability.PNP
