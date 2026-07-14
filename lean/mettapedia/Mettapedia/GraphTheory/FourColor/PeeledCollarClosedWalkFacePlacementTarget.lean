import Mettapedia.GraphTheory.FourColor.PeeledCollarAttachmentFaceSourceDataEquiv

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk-source face-placement target for one carrier cut.  This names the
next planar separator fact: choose a cut-compatible ambient side, and for each
pair of attachments of one off-carrier component choose a common placement
face whose selected boundary edges do not cross that side.
-/
def CutOffCarrierAttachmentFacePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)) :
    Prop :=
  ∃ side : V → Prop,
    (∀ w : BoundaryEdgeSetEndpointVertex
        (G := G)
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet,
      side (source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryEmbedding w) ↔
        cut.side w) ∧
      ∀ root : V,
        ∀ a b : BoundaryEdgeSetEndpointVertex
            (G := G)
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet,
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G)
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root a →
          BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
            (G := G)
            source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root b →
            ∃ f : AmbientFace emb.faces,
              PlanarBoundaryAnnulusBoundaryData.OffCarrierAttachmentFacePlacementOn
                  source.toPlanarBoundaryAnnulusBoundaryData root a b f ∧
                PlanarBoundaryAnnulusBoundaryData.FaceSelectedBoundaryEdgesDoNotCrossSide
                  source.toPlanarBoundaryAnnulusBoundaryData side f

/--
All-cuts closed-walk-source face-placement target.  This is the reusable
foundation target still owed by the planar normal-form layer.
-/
def OffCarrierAttachmentFacePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet),
    source.CutOffCarrierAttachmentFacePlacementNoncrossingTarget cut

/--
The closed-walk-source face-placement target supplies chosen source-side
attachment-face data on the extracted annulus boundary split.
-/
theorem attachmentFaceSourceDataTarget_of_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
      source.toPlanarBoundaryAnnulusBoundaryData := by
  intro cut
  rcases h cut with ⟨side, hside, hroute⟩
  refine
    ⟨{ side := side
       side_comp_cut := hside
       placement := ?_ }, ?_⟩
  · intro root a b hrootA hrootB
    rcases hroute root a b hrootA hrootB with
      ⟨f, hplacement, _hnoncross⟩
    exact ⟨f, hplacement⟩
  · intro root a b hrootA hrootB
    exact hroute root a b hrootA hrootB

/--
The closed-walk-source face-placement target is exactly the chosen source-data
target on the source's extracted annulus boundary split.
-/
theorem facePlacementNoncrossingTarget_iff_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.OffCarrierAttachmentFacePlacementNoncrossingTarget ↔
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData := by
  constructor
  · exact source.attachmentFaceSourceDataTarget_of_facePlacementNoncrossingTarget
  · intro h cut
    rcases h cut with ⟨sourceData, hnoncross⟩
    refine ⟨sourceData.side, sourceData.side_comp_cut, ?_⟩
    intro root a b hrootA hrootB
    exact hnoncross root a b hrootA hrootB

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical closed-walk-source cyclic five-edge-connectivity from the named
face-placement noncrossing foundation target.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    regime source hboundary
    (source.attachmentFaceSourceDataTarget_of_facePlacementNoncrossingTarget h)

/--
Canonical closed-walk-source S4 salvage through inherited cyclic
five-edge-connectivity from the named face-placement target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
      regime source hboundary h)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired closed-walk-source cyclic five-edge-connectivity from the named
face-placement noncrossing foundation target.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
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
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    regime source hboundary
    (source.attachmentFaceSourceDataTarget_of_facePlacementNoncrossingTarget h)

/--
Repaired closed-walk-source S4 salvage through inherited cyclic
five-edge-connectivity from the named face-placement target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
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
    (h : source.OffCarrierAttachmentFacePlacementNoncrossingTarget) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
      regime source hboundary h)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Closed-walk-source canonical-annulus S4 target using the named
face-placement noncrossing foundation obligation.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget :
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
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical closed-walk face-placement target S4 statement. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
      regime source hboundary h

/--
Closed-walk-source repaired-annulus S4 target using the named
face-placement noncrossing foundation obligation.
-/
def
    Section92Step4RepairedAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget :
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
      source.OffCarrierAttachmentFacePlacementNoncrossingTarget →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired closed-walk face-placement target S4 statement. -/
theorem
    section92Step4RepairedAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkFacePlacementNoncrossingThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_facePlacementNoncrossingTarget
      regime source hboundary h

end Mettapedia.GraphTheory.FourColor
