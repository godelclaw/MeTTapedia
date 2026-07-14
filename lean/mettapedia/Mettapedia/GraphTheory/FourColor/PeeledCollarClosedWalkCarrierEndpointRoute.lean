import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkCutAvoidingFaceRouteIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Closed-walk mapped-cut route bridges into the carrier-endpoint interface.

The closed-walk mapped-cut face-route input structure is the source-level
version of the planar foundation used by the CAP5-free route.  This module
exposes the same input through the off-carrier walk-consistency and
carrier-endpoint support APIs, so source-level users do not need to pass
through the CAP5-free package to get the endpoint-support consequences.
-/

variable {V : Type} [DecidableEq V]

namespace ClosedWalkMappedCutAvoidingFaceRouteInputs

/-- Closed-walk mapped-cut face-route inputs supply off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget :=
  source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
    inputs.mappedCutAvoidingFaceRoute

/-- Closed-walk mapped-cut face-route inputs supply carrier-endpoint support. -/
theorem carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
      inputs.offCarrierWalkConsistencyTarget

/--
Closed-walk mapped-cut face-route inputs supply boundary-support data for the
selected induced boundary embedding.
-/
theorem ambientSideBoundarySupportsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
      inputs.carrierEndpointSupportTarget

/--
Closed-walk mapped-cut face-route inputs supply off-boundary no-crossing data
for the selected induced boundary embedding.
-/
theorem ambientSideOffBoundaryNoCrossingsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports
    inputs.ambientSideBoundarySupportsToAmbient

/--
Closed-walk mapped-cut face-route inputs expose the carrier-endpoint route
consequences at source level.
-/
theorem carrierEndpointRouteConsequences
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb}
    (inputs : ClosedWalkMappedCutAvoidingFaceRouteInputs source) :
    source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierWalkConsistencyTarget ∧
      source.toPlanarBoundaryAnnulusBoundaryData.PeeledCollarCarrierEndpointSupportTarget ∧
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  ⟨inputs.offCarrierWalkConsistencyTarget,
    inputs.carrierEndpointSupportTarget,
    inputs.ambientSideBoundarySupportsToAmbient,
    inputs.ambientSideOffBoundaryNoCrossingsToAmbient,
    inputs.peeledCollarSmallCyclicCutLiftsToAmbient,
    inputs.cyclicallyFiveEdgeConnected,
    inputs.closedCollarForbidsCyclicTwoCut,
    inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end ClosedWalkMappedCutAvoidingFaceRouteInputs

namespace CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

/-- Canonical mapped-cut face-route inputs supply off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget := by
  have hoffSource :
      inputs.source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierWalkConsistencyTarget :=
    inputs.source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
      inputs.mappedCutAvoidingFaceRoute
  change data.boundaryData.PeeledCollarOffCarrierWalkConsistencyTarget
  rw [inputs.boundaryData_eq_source]
  exact hoffSource

/-- Canonical mapped-cut face-route inputs supply carrier-endpoint support. -/
theorem carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarCarrierEndpointSupportTarget :=
  data.boundaryData.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
    inputs.offCarrierWalkConsistencyTarget

/-- Canonical mapped-cut face-route inputs supply boundary-support data. -/
theorem ambientSideBoundarySupportsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient data.inducedBoundaryEmbedding :=
  data.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
    inputs.carrierEndpointSupportTarget

/-- Canonical mapped-cut face-route inputs supply off-boundary no-crossing data. -/
theorem ambientSideOffBoundaryNoCrossingsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient data.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports
    inputs.ambientSideBoundarySupportsToAmbient

/-- Canonical mapped-cut face-route inputs supply the small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    inputs.offCarrierWalkConsistencyTarget

/--
Canonical mapped-cut face-route inputs expose the carrier-endpoint route
consequences.
-/
theorem carrierEndpointRouteConsequences
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (inputs : CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ∧
      data.PeeledCollarCarrierEndpointSupportTarget ∧
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        data.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  ⟨inputs.offCarrierWalkConsistencyTarget,
    inputs.carrierEndpointSupportTarget,
    inputs.ambientSideBoundarySupportsToAmbient,
    inputs.ambientSideOffBoundaryNoCrossingsToAmbient,
    inputs.peeledCollarSmallCyclicCutLiftsToAmbient,
    inputs.cyclicallyFiveEdgeConnected,
    inputs.closedCollarForbidsCyclicTwoCut,
    inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

namespace RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

/-- Repaired mapped-cut face-route inputs supply off-carrier walk consistency. -/
theorem offCarrierWalkConsistencyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget := by
  have hoffSource :
      inputs.source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierWalkConsistencyTarget :=
    inputs.source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
      inputs.mappedCutAvoidingFaceRoute
  change data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
    |>.PeeledCollarOffCarrierWalkConsistencyTarget
  rw [inputs.boundaryData_eq_source]
  exact hoffSource

/-- Repaired mapped-cut face-route inputs supply carrier-endpoint support. -/
theorem carrierEndpointSupportTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarCarrierEndpointSupportTarget :=
  data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
    |>.carrierEndpointSupportTarget_of_offCarrierWalkConsistencyTarget
      inputs.offCarrierWalkConsistencyTarget

/-- Repaired mapped-cut face-route inputs supply boundary-support data. -/
theorem ambientSideBoundarySupportsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarCutAmbientSideBoundarySupportsToAmbient data.inducedBoundaryEmbedding :=
  data.peeledCollarCutAmbientSideBoundarySupportsToAmbient_of_carrierEndpointSupportTarget
    inputs.carrierEndpointSupportTarget

/-- Repaired mapped-cut face-route inputs supply off-boundary no-crossing data. -/
theorem ambientSideOffBoundaryNoCrossingsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient data.inducedBoundaryEmbedding :=
  peeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient_of_ambientSideBoundarySupports
    inputs.ambientSideBoundarySupportsToAmbient

/-- Repaired mapped-cut face-route inputs supply the small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph :=
  data.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
    inputs.offCarrierWalkConsistencyTarget

/--
Repaired mapped-cut face-route inputs expose the carrier-endpoint route
consequences.
-/
theorem carrierEndpointRouteConsequences
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (inputs : RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data) :
    data.PeeledCollarOffCarrierWalkConsistencyTarget ∧
      data.PeeledCollarCarrierEndpointSupportTarget ∧
      PeeledCollarCutAmbientSideBoundarySupportsToAmbient
        data.inducedBoundaryEmbedding ∧
      PeeledCollarCutAmbientSideOffBoundaryNoCrossingsToAmbient
        data.inducedBoundaryEmbedding ∧
      PeeledCollarSmallCyclicCutLiftsToAmbient G data.inducedBoundaryGraph ∧
      CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
      ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
      ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
        data.inducedBoundaryGraph :=
  ⟨inputs.offCarrierWalkConsistencyTarget,
    inputs.carrierEndpointSupportTarget,
    inputs.ambientSideBoundarySupportsToAmbient,
    inputs.ambientSideOffBoundaryNoCrossingsToAmbient,
    inputs.peeledCollarSmallCyclicCutLiftsToAmbient,
    inputs.cyclicallyFiveEdgeConnected,
    inputs.closedCollarForbidsCyclicTwoCut,
    inputs.closedCollarWindingFreedomEscape_not_simplyRealizable⟩

end RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs

end Mettapedia.GraphTheory.FourColor
