import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkCutAvoidingFaceRouteIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Source-level face-placement foundation target for the regime route.  This is
the remaining planar-normal-form theorem needed upstream of the cut-lift
bridge: every small cyclic collar cut admits a cut-compatible ambient side
and common noncrossing face placements for same-component off-carrier
attachments.
-/
def RegimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  source.OffCarrierAttachmentFacePlacementNoncrossingTarget

/-- The named foundation target is definitionally the closed-walk face-placement target. -/
theorem regimeFacePlacementFoundationTarget_iff_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.RegimeFacePlacementFoundationTarget ↔
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget :=
  Iff.rfl

/-- The face-placement foundation target builds the closed-walk route inputs. -/
def closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ClosedWalkMappedCutAvoidingFaceRouteInputs source :=
  ClosedWalkMappedCutAvoidingFaceRouteInputs.of_facePlacementNoncrossingTarget
    source regime h

/-- The foundation target supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  (source.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime h).peeledCollarSmallCyclicCutLiftsToAmbient

/-- The foundation target supplies cyclic five-edge-connectivity for the source collar. -/
theorem cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    CyclicallyFiveEdgeConnected
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  (source.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime h).cyclicallyFiveEdgeConnected

/-- The foundation target supplies the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ClosedCollarForbidsCyclicTwoCut
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  (source.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime h).closedCollarForbidsCyclicTwoCut

/-- The foundation target supplies the S4 winding salvage for the source collar. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  (source.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime h).closedCollarWindingFreedomEscape_not_simplyRealizable

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical closed-walk route inputs from the face-placement foundation target,
aligned with the canonical annulus boundary data.
-/
def closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data :=
  CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs.of_facePlacementNoncrossingTarget
    data regime source hboundary h

/-- The canonical aligned foundation target supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h).cyclicallyFiveEdgeConnected

/-- The canonical aligned foundation target supplies the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h).closedCollarForbidsCyclicTwoCut

/-- The canonical aligned foundation target supplies S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired closed-walk route inputs from the face-placement foundation target,
aligned with the repaired previous-boundary annulus data.
-/
def closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs data :=
  RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteInputs.of_facePlacementNoncrossingTarget
    data regime source hboundary h

/-- The repaired aligned foundation target supplies cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h).cyclicallyFiveEdgeConnected

/-- The repaired aligned foundation target supplies the no-cyclic-two-cut consequence. -/
theorem closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h).closedCollarForbidsCyclicTwoCut

/-- The repaired aligned foundation target supplies S4 winding salvage. -/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.RegimeFacePlacementFoundationTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph :=
  (data.closedWalkMappedCutAvoidingFaceRouteInputs_of_regimeFacePlacementFoundationTarget
    regime source hboundary h)
      |>.closedCollarWindingFreedomEscape_not_simplyRealizable

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Source-level index target: the face-placement foundation theorem is exactly
what remains before the source route supplies small-cut lift, cyclic
five-edge-connectivity, no cyclic two-cut, and S4 salvage.
-/
def Section92Step4ClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph),
      source.RegimeFacePlacementFoundationTarget →
        PeeledCollarSmallCyclicCutLiftsToAmbient G
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim source-level route index for the face-placement foundation target. -/
theorem section92Step4ClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Section92Step4ClosedWalkRegimeFacePlacementFoundationRouteIndexTarget := by
  intro V _ G emb source regime h
  exact
    ⟨source.peeledCollarSmallCyclicCutLiftsToAmbient_of_regimeFacePlacementFoundationTarget
        regime h,
      source.cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
        regime h,
      source.closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
        regime h,
      source.closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
        regime h⟩

/--
Canonical aligned index target for the face-placement foundation theorem and
the downstream cyclic-connectivity/S4 consequences.
-/
def Section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData →
      source.RegimeFacePlacementFoundationTarget →
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical aligned route index for the face-placement foundation target. -/
theorem section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Section92Step4CanonicalClosedWalkRegimeFacePlacementFoundationRouteIndexTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    ⟨data.cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
        regime source hboundary h,
      data.closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
        regime source hboundary h,
      data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
        regime source hboundary h⟩

/--
Repaired aligned index target for the face-placement foundation theorem and
the downstream cyclic-connectivity/S4 consequences.
-/
def Section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData =
        source.toPlanarBoundaryAnnulusBoundaryData →
      source.RegimeFacePlacementFoundationTarget →
        CyclicallyFiveEdgeConnected data.inducedBoundaryGraph ∧
        ClosedCollarForbidsCyclicTwoCut data.inducedBoundaryGraph ∧
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired aligned route index for the face-placement foundation target. -/
theorem section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget :
    Section92Step4RepairedClosedWalkRegimeFacePlacementFoundationRouteIndexTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    ⟨data.cyclicallyFiveEdgeConnected_of_regimeFacePlacementFoundationTarget
        regime source hboundary h,
      data.closedCollarForbidsCyclicTwoCut_of_regimeFacePlacementFoundationTarget
        regime source hboundary h,
      data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_regimeFacePlacementFoundationTarget
        regime source hboundary h⟩

end Mettapedia.GraphTheory.FourColor
