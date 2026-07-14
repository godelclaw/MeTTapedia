import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkSplitConnectivity

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
Chosen attachment-face source data for one carrier cut.  Unlike the stronger
noncrossing-upgrade target, this package records the single ambient side and
single placement family produced by the planar normal-form argument for the
cut under consideration.
-/
structure CutOffCarrierAttachmentFaceSourceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)) where
  side : V → Prop
  side_comp_cut :
    ∀ w : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet,
      side (data.inducedBoundaryEmbedding w) ↔ cut.side w
  placement :
    ∀ root : V,
      ∀ a b : BoundaryEdgeSetEndpointVertex
          (G := G) data.ambientBoundaryEdgeSet,
        BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
          (G := G) data.ambientBoundaryEdgeSet root a →
        BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
          (G := G) data.ambientBoundaryEdgeSet root b →
          ∃ f : AmbientFace emb.faces,
            data.OffCarrierAttachmentFacePlacementOn root a b f

namespace CutOffCarrierAttachmentFaceSourceData

/--
The selected source data is noncrossing when each attachment pair admits a
chosen placement face whose selected boundary edges do not cross the recorded
ambient side.
-/
def Noncrossing
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (source : data.CutOffCarrierAttachmentFaceSourceData cut) : Prop :=
  ∀ root : V,
    ∀ a b : BoundaryEdgeSetEndpointVertex
        (G := G) data.ambientBoundaryEdgeSet,
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) data.ambientBoundaryEdgeSet root a →
      BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
        (G := G) data.ambientBoundaryEdgeSet root b →
        ∃ f : AmbientFace emb.faces,
          data.OffCarrierAttachmentFacePlacementOn root a b f ∧
            data.FaceSelectedBoundaryEdgesDoNotCrossSide source.side f

/-- The chosen source data forgets to the split attachment-face source target. -/
theorem toCutOffCarrierAttachmentFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (source : data.CutOffCarrierAttachmentFaceSourceData cut) :
    data.CutOffCarrierAttachmentFaceSourceTarget cut := by
  exact ⟨source.side, source.side_comp_cut, source.placement⟩

/--
The chosen source data plus its noncrossing proof supplies the existing
face-source target consumed by the selected-boundary-arc bridge.
-/
theorem toCutOffCarrierAttachmentNoncrossingFaceSourceTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    {cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet)}
    (source : data.CutOffCarrierAttachmentFaceSourceData cut)
    (hnoncross : source.Noncrossing) :
    data.CutOffCarrierAttachmentNoncrossingFaceSourceTarget cut := by
  refine ⟨source.side, source.side_comp_cut, ?_⟩
  intro root a b hrootA hrootB
  rcases hnoncross root a b hrootA hrootB with
    ⟨f, hplacement, hfaceNoncross⟩
  rcases hplacement with
    ⟨e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb⟩
  exact
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb,
      hfaceNoncross⟩

end CutOffCarrierAttachmentFaceSourceData

/--
All-cuts chosen attachment-face source target.  This is the narrow
source-side version of the remaining planar-normal-form face obligation.
-/
def PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet),
    ∃ source : data.CutOffCarrierAttachmentFaceSourceData cut,
      source.Noncrossing

/-- The chosen source-data target forgets to the split attachment-face target. -/
theorem attachmentFaceSourceTarget_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget) :
    data.PeeledCollarOffCarrierAttachmentFaceSourceTarget := by
  intro cut
  rcases h cut with ⟨source, _⟩
  exact source.toCutOffCarrierAttachmentFaceSourceTarget

/-- The chosen source-data target supplies the existing noncrossing face source target. -/
theorem attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (h : data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingFaceSourceTarget := by
  intro cut
  rcases h cut with ⟨source, hnoncross⟩
  exact source.toCutOffCarrierAttachmentNoncrossingFaceSourceTarget hnoncross

/--
Chosen attachment-face source data, together with selected-boundary arc
geometry, supplies the selected-boundary-arc source target used by the
cut-lift route.
-/
theorem attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusBoundaryData emb}
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h : data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget) :
    data.PeeledCollarOffCarrierAttachmentNoncrossingSelectedBoundaryArcSourceTarget :=
  data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_faceSourceTarget
    harc
    (data.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h)

end PlanarBoundaryAnnulusBoundaryData

/-- Canonical annulus chosen attachment-face source-data target. -/
def PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget

/-- Repaired annulus chosen attachment-face source-data target. -/
def PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Prop :=
  data.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget

namespace MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

/--
Canonical-annulus upstream inheritance from chosen source-side attachment-face
data.
-/
theorem cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      harc h)

/--
Canonical-annulus S4 salvage from chosen source-side attachment-face data,
routed through inherited cyclic five-edge-connectivity.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      regime harc h)

end MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs

namespace MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

/-- Repaired-annulus upstream inheritance from chosen source-side attachment-face data. -/
theorem cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      harc h)

/--
Repaired-annulus S4 salvage from chosen source-side attachment-face data,
routed through inherited cyclic five-edge-connectivity.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (cyclicallyFiveEdgeConnected_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      regime harc h)

end MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical closed-walk-source cyclic five-edge-connectivity from chosen
source-side attachment-face data.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary
      (source.toPlanarBoundaryAnnulusBoundaryData
        |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h))

/--
Canonical closed-walk-source S4 salvage from chosen source-side
attachment-face data, routed through inherited cyclic five-edge-connectivity.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
      regime source hboundary h)

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired closed-walk-source cyclic five-edge-connectivity from chosen
source-side attachment-face data.
-/
theorem cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
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
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    CyclicallyFiveEdgeConnected data.inducedBoundaryGraph :=
  MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.cyclicallyFiveEdgeConnected_of_noncrossingSelectedBoundaryArcSourceTarget
    regime
    (data.attachmentNoncrossingSelectedBoundaryArcSourceTarget_of_closedWalkAnnulusBoundarySource_faceSourceTarget
      source hboundary
      (source.toPlanarBoundaryAnnulusBoundaryData
        |>.attachmentNoncrossingFaceSourceTarget_of_attachmentFaceSourceDataTarget h))

/--
Repaired closed-walk-source S4 salvage from chosen source-side
attachment-face data, routed through inherited cyclic five-edge-connectivity.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
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
    (h :
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData) :
    ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
      data.inducedBoundaryGraph :=
  closedCollarWindingFreedomSeparatorEquippedEscape_not_realizable_of_cyclicallyFiveEdgeConnected
    (data.cyclicallyFiveEdgeConnected_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
      regime source hboundary h)

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
End-to-end canonical-annulus S4 target using chosen source-side attachment-face
data and selected-boundary arc geometry.
-/
def
    Section92Step4CanonicalAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      (∀ f : AmbientFace emb.faces,
        BoundarySelectedBoundaryArcOnFace (emb := emb) f) →
      PlanarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical-annulus chosen-source-data S4 statement. -/
theorem
    section92Step4CanonicalAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc h
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      regime harc h

/--
End-to-end repaired-annulus S4 target using chosen source-side attachment-face
data and selected-boundary arc geometry.
-/
def
    Section92Step4RepairedAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (_ :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph),
      (∀ f : AmbientFace emb.faces,
        BoundarySelectedBoundaryArcOnFace (emb := emb) f) →
      PlanarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        data →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired-annulus chosen-source-data S4 statement. -/
theorem
    section92Step4RepairedAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusAttachmentFaceSourceDataRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime harc h
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_boundarySelectedBoundaryArcOnFace_of_attachmentFaceSourceDataTarget
      regime harc h

/--
Closed-walk-source canonical-annulus S4 target using chosen source-side
attachment-face data.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical closed-walk chosen-source-data S4 statement through connectivity. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
      regime source hboundary h

/--
Closed-walk-source repaired-annulus S4 target using chosen source-side
attachment-face data.
-/
def
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget :
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
      PlanarBoundaryAnnulusBoundaryData.PeeledCollarOffCarrierAttachmentFaceSourceDataTarget
        source.toPlanarBoundaryAnnulusBoundaryData →
        ¬ ClosedCollarWindingFreedomSeparatorEquippedEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired closed-walk chosen-source-data S4 statement through connectivity. -/
theorem
    section92Step4RepairedAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkAttachmentFaceSourceDataThroughConnectivityRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_throughConnectivity_of_closedWalkAnnulusBoundarySource_attachmentFaceSourceDataTarget
      regime source hboundary h

end Mettapedia.GraphTheory.FourColor
