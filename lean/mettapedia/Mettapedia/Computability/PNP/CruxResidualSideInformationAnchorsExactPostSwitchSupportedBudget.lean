import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchActiveOrbit

/-!
# PNP residual-side-information anchors: exact post-switch supported budget

This module records the supported obstruction package, absence of visible-pair
balancing, and full residual-resolution budget on the active orbit.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit already realizes the full
supported proof-relevant residual obstruction package with the actual
successful classifier, and therefore rules out supportwise visible-pair
balancing on that same visible surface. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_supported_obstruction_package_and_no_visible_pair_balancing
    {Z : Type*} [Fintype Z] (z0 : Z) :
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
          ¬ SourceOnlyPredicateCapturesSideEq
            invariantVisibleData
            (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b) (u.b)) ∧
      (∃ u : ExactVisiblePostSwitchSurface Z 1,
        0 < activeOrbitWeight z0 u ∧
          activeOrbitClassifier (activeOrbitFeatures (tiInputMap u)) ≠
            activeOrbitClassifier (activeOrbitFeatures u)) ∧
      ¬ SupportwiseVisiblePairBalancing
          invariantVisibleData
          (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
          activeOrbitTarget
          (activeOrbitWeight z0) := by
  exact
    exactPostSwitch_activeOrbit_realizes_supported_obstruction_package_and_no_visiblePairBalancing
      (Z := Z) z0

/-- Route-coverage anchor: on the manuscript's exact visible post-switch
surface, the concrete active two-point orbit does not merely have positive
resolving mass.  Its successful classifier uses the entire supported mass as
residual-resolving mass, and its doubled advantage is exactly that same
resolving budget. -/
theorem residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_full_resolution_budget
    {Z : Type*} [Fintype Z] (z0 : Z) :
    resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) =
      weightedTotalMass (activeOrbitWeight z0) ∧
    doubledAdvantage
        activeOrbitFeatures
        activeOrbitTarget
        (activeOrbitWeight z0)
        activeOrbitClassifier =
      resolvedMass tiInputMap
        (fun u : ExactVisiblePostSwitchSurface Z 1 => u.b)
        (activeOrbitWeight z0) := by
  exact ⟨resolvedMass_activeOrbit_eq_weightedTotalMass (Z := Z) z0,
    doubledAdvantage_activeOrbit_eq_resolvedMass (Z := Z) z0⟩

end Mettapedia.Computability.PNP
