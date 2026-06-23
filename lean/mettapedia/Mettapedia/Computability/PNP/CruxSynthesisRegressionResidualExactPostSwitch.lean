import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchActiveOrbit
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchSupportedBudget
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExactPostSwitchFork

/-!
# Regression checks for PNP residual-side-information anchors: exact post-switch active-orbit residual package checks

This module is part of the decomposed residual-side-information regression
ledger.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while separating residual-anchor checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_exact_post_switch_active_orbit_pure_package_regression
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
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_pure_residual_package
      (Z := Z) z0

theorem residual_side_information_anchor_exact_post_switch_active_orbit_prediction_witness_regression
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
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_prediction_witness
      (Z := Z) z0

theorem residual_side_information_anchor_exact_post_switch_active_orbit_supported_obstruction_package_and_no_visible_pair_balancing_regression
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
          (activeOrbitWeight z0) := by
  exact
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_supported_obstruction_package_and_no_visible_pair_balancing
      (Z := Z) z0

theorem residual_side_information_anchor_exact_post_switch_active_orbit_full_resolution_budget_regression
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
  exact
    residualSideInformationCoverage_anchor_exactPostSwitch_activeOrbit_full_resolution_budget
      (Z := Z) z0

end Mettapedia.Computability.PNP.CruxSynthesisRegression
