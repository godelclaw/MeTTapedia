import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# PNP residual-side-information counterexample coverage

This module packages the broad residual-side-information counterexample layer.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The concrete counterexample layer for broad residual-side-information
coverage: same-base residual collisions block source-only decoding, the
orbit-invisible counterexample has zero resolved mass and no successful
classifier on its visible surface, and the balanced counterexample blocks all
classifiers by a surviving visible-pair-balancing involution. -/
def ResidualSideInformationCounterexampleCoverage : Prop :=
  (∀ {Ω Base Side : Type} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω},
      base x = base y →
        side x ≠ side y →
          ¬ SideInfoDeterminedBy base side) ∧
  (Function.Involutive OrbitInvisibleResidualCounterexample.orbitSwap ∧
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
          OrbitInvisibleResidualCounterexample.weight h)) ∧
  (∃ h : Unit × Bool → Bool,
    0 < resolvedMass
      BalancedResidualCounterexample.resolveSwap
      BalancedResidualCounterexample.side
      BalancedResidualCounterexample.weight ∧
    ¬ SideInfoDeterminedBy
      BalancedResidualCounterexample.base
      BalancedResidualCounterexample.side ∧
    ¬ SupportwiseSourceOnlyPairClassifier
      BalancedResidualCounterexample.base
      BalancedResidualCounterexample.side
      BalancedResidualCounterexample.weight h ∧
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
    (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
      h
          (BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.resolveSwap x),
            BalancedResidualCounterexample.side
              (BalancedResidualCounterexample.resolveSwap x)) ≠
        h
          (BalancedResidualCounterexample.base x,
            BalancedResidualCounterexample.side x)) ∧
    Function.Involutive BalancedResidualCounterexample.neutralSwap ∧
    (∀ x, BalancedResidualCounterexample.target
        (BalancedResidualCounterexample.neutralSwap x) =
          !(BalancedResidualCounterexample.target x)) ∧
    (∀ x, BalancedResidualCounterexample.weight
        (BalancedResidualCounterexample.neutralSwap x) =
          BalancedResidualCounterexample.weight x) ∧
    (∀ x, 0 < BalancedResidualCounterexample.weight x →
      (BalancedResidualCounterexample.base
          (BalancedResidualCounterexample.neutralSwap x),
        BalancedResidualCounterexample.side
          (BalancedResidualCounterexample.neutralSwap x)) =
        (BalancedResidualCounterexample.base x,
          BalancedResidualCounterexample.side x)) ∧
    (∀ h' : Unit × Bool → Bool,
      ¬ 0 < doubledAdvantage
        (fun x =>
          (BalancedResidualCounterexample.base x,
            BalancedResidualCounterexample.side x))
        BalancedResidualCounterexample.target
        BalancedResidualCounterexample.weight h') ∧
    (∀ h' : Unit × Bool → Bool,
      ¬ weightedTotalMass BalancedResidualCounterexample.weight <
        2 * weightedCorrectMass
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h'))

@[simp] theorem residualSideInformationCounterexampleCoverage :
    ResidualSideInformationCounterexampleCoverage := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω Base Side base side x y hbase hside
    exact
      residualSideInformationCoverage_anchor_collision_blocks_source_decoder
        hbase hside
  · exact
      residualSideInformationCoverage_anchor_supported_non_source_determined_not_sufficient_for_positive_resolvedMass_or_success
  · exact
      residualSideInformationCoverage_anchor_supported_obstruction_package_with_visible_pair_balancing_blocks_any_success

end Mettapedia.Computability.PNP
