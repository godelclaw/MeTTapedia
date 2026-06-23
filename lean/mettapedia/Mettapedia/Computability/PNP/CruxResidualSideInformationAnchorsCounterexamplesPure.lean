import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassCollisions
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassSourceDetermined
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCollisionMassResolvedMass
import Mettapedia.Computability.PNP.ResidualSideInformationPureResidualGap
import Mettapedia.Computability.PNP.ResidualSideInformationNonSourceDeterminedGap
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCollapse

/-!
# PNP residual-side-information anchors: pure and orbit-invisible counterexamples

These concrete surfaces show that pure residual obstruction data and supported
non-source-determined variation are not, by themselves, success criteria.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: the pure residual obstruction package is strictly
weaker than successful residual repair.  The concrete balanced four-point
surface has positive resolved mass and the full classifier-free obstruction
package, but no classifier on `(base, side)` can beat chance or strict half
accuracy. -/
theorem residualSideInformationCoverage_anchor_pure_residual_obstruction_not_sufficient_for_success
    :
    Function.Involutive BalancedResidualCounterexample.resolveSwap ∧
      (∀ x, BalancedResidualCounterexample.base
          (BalancedResidualCounterexample.resolveSwap x) =
            BalancedResidualCounterexample.base x) ∧
      (∀ x, BalancedResidualCounterexample.target
          (BalancedResidualCounterexample.resolveSwap x) =
            !(BalancedResidualCounterexample.target x)) ∧
      (∀ x, BalancedResidualCounterexample.weight
          (BalancedResidualCounterexample.resolveSwap x) =
            BalancedResidualCounterexample.weight x) ∧
      0 < resolvedMass
        BalancedResidualCounterexample.resolveSwap
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      ¬ SideInfoDeterminedBy
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side ∧
      PositiveWeightSideInfoCollisionOverBase
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.resolveSwap x) =
          BalancedResidualCounterexample.base x ∧
        BalancedResidualCounterexample.side
            (BalancedResidualCounterexample.resolveSwap x) ≠
          BalancedResidualCounterexample.side x) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          BalancedResidualCounterexample.base
          BalancedResidualCounterexample.side
          (BalancedResidualCounterexample.side x)) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass BalancedResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (BalancedResidualCounterexample.base x,
                BalancedResidualCounterexample.side x))
            BalancedResidualCounterexample.target
            BalancedResidualCounterexample.weight h) := by
  exact BalancedResidualCounterexample.route_package

/-- Route-coverage anchor: even supported non-source-determined residual
variation can still be completely invisible to the involution.  The concrete
orbit-invisible four-point surface has positive-support same-base residual
variation and is not source-determined, but its residual side channel stays
constant on every involution orbit.  So the resolved mass is zero, even a
concrete residual-reading classifier on `(base, side)` can fail to be
supportwise source-only while still staying exactly at chance, and in fact no
classifier on `(base, side)` can beat chance or strict half accuracy. -/
theorem residualSideInformationCoverage_anchor_supported_non_source_determined_not_sufficient_for_positive_resolvedMass_or_success
    :
    Function.Involutive OrbitInvisibleResidualCounterexample.orbitSwap ∧
      (∀ x, OrbitInvisibleResidualCounterexample.base
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.base x) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.side
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.side x) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.target
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            !(OrbitInvisibleResidualCounterexample.target x)) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.weight
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.weight x) ∧
      ¬ SideInfoDeterminedBy
        OrbitInvisibleResidualCounterexample.base
        OrbitInvisibleResidualCounterexample.side ∧
      PositiveWeightSideInfoCollisionOverBase
        OrbitInvisibleResidualCounterexample.base
        OrbitInvisibleResidualCounterexample.side
        OrbitInvisibleResidualCounterexample.weight ∧
      (∃ x, 0 < OrbitInvisibleResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          OrbitInvisibleResidualCounterexample.base
          OrbitInvisibleResidualCounterexample.side
          (OrbitInvisibleResidualCounterexample.side x)) ∧
      resolvedMass
        OrbitInvisibleResidualCounterexample.orbitSwap
        OrbitInvisibleResidualCounterexample.side
        OrbitInvisibleResidualCounterexample.weight = 0 ∧
      (∃ h : Unit × Bool → Bool,
        ¬ SupportwiseSourceOnlyPairClassifier
          OrbitInvisibleResidualCounterexample.base
          OrbitInvisibleResidualCounterexample.side
          OrbitInvisibleResidualCounterexample.weight h ∧
        ¬ 0 < doubledAdvantage
          (fun x =>
            (OrbitInvisibleResidualCounterexample.base x,
              OrbitInvisibleResidualCounterexample.side x))
          OrbitInvisibleResidualCounterexample.target
          OrbitInvisibleResidualCounterexample.weight h ∧
        ¬ weightedTotalMass OrbitInvisibleResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (OrbitInvisibleResidualCounterexample.base x,
                OrbitInvisibleResidualCounterexample.side x))
            OrbitInvisibleResidualCounterexample.target
            OrbitInvisibleResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (OrbitInvisibleResidualCounterexample.base x,
              OrbitInvisibleResidualCounterexample.side x))
          OrbitInvisibleResidualCounterexample.target
          OrbitInvisibleResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass OrbitInvisibleResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (OrbitInvisibleResidualCounterexample.base x,
                OrbitInvisibleResidualCounterexample.side x))
            OrbitInvisibleResidualCounterexample.target
            OrbitInvisibleResidualCounterexample.weight h) := by
  exact OrbitInvisibleResidualCounterexample.route_package

end Mettapedia.Computability.PNP
