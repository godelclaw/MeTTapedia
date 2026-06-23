import Mettapedia.Computability.PNP.ResidualSideInformationObstruction
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantPerfect
import Mettapedia.Computability.PNP.ResolutionDemandObstructionAdvantage
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPairBounds
import Mettapedia.Computability.PNP.ResolutionDemandObstructionResolvedMass
import Mettapedia.Computability.PNP.ResolutionDemandObstructionPrediction
import Mettapedia.Computability.PNP.ResolutionDemandObstructionWitnesses

/-!
# PNP residual-side-information anchors: source-fiber collisions

This module collects direct source-fiber collision anchors and the toy
two-point residual collision witness.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- Route-coverage anchor: a same-source/different-residual collision cannot
be decoded from the source summary alone. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_decoder
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SideInfoDeterminedBy base side :=
  not_sideInfoDeterminedBy_of_same_base_ne_side hbase hside

/-- Route-coverage anchor: the equality predicate for one residual value cannot
be pushed down to a source-only predicate across a same-source collision. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_predicate
    {Ω Base Side : Type*} {base : Ω → Base} {side : Ω → Side}
    {x y : Ω} (hbase : base x = base y) (hside : side x ≠ side y) :
    ¬ SourceOnlyPredicateCapturesSideEq base side (side x) :=
  not_sourceOnlyPredicateCapturesSideEq_left_of_same_base_ne_side hbase hside

/-- Route-coverage anchor: a Boolean residual target that varies inside one
source-summary fiber cannot be recovered by a source-only classifier. -/
theorem residualSideInformationCoverage_anchor_collision_blocks_source_boolean_classifier
    {Ω Base : Type*} {base : Ω → Base} {target : Ω → Bool}
    {x y : Ω} (hbase : base x = base y) (htarget : target x ≠ target y) :
    ¬ SourceOnlyBooleanClassifier base target :=
  not_sourceOnlyBooleanClassifier_of_same_base_ne_target hbase htarget

/-- Route-coverage anchor: a concrete two-point same-source residual collision
witnesses that source-only residual decoding is not automatic. -/
theorem residualSideInformationCoverage_anchor_toy_collision :
    SideInfoCollisionOverBase residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SideInfoDeterminedBy residualSideInfoToyBase residualSideInfoToySide ∧
      ¬ SourceOnlyPredicateCapturesSideEq
        residualSideInfoToyBase residualSideInfoToySide false ∧
      ¬ SourceOnlyBooleanClassifier
        residualSideInfoToyBase residualSideInfoToySide := by
  exact
    ⟨residualSideInfoToy_collision,
      residualSideInfoToy_not_determinedBy_base,
      residualSideInfoToy_not_sourceOnlyPredicate_false,
      residualSideInfoToy_not_sourceOnlyBooleanClassifier⟩

end Mettapedia.Computability.PNP
