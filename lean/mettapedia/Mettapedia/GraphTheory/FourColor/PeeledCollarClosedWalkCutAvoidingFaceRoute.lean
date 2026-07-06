import Mettapedia.GraphTheory.FourColor.PeeledCollarClosedWalkFacePlacementConnectivity

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Cut-avoiding face-route target for one carrier cut.  This is the face-local
Jordan/annulus separation obligation still owed by the planar-normal-form
layer: two attachments of the same off-carrier component can be placed on
selected boundary edges of one face, and the selected-boundary walk on that
face avoids the mapped carrier cut.
-/
def CutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)) :
    Prop :=
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
        ∃ e₁ e₂ : G.edgeSet,
        ∃ _ : e₁ ∈ emb.faceBoundary f.1,
        ∃ _ : e₂ ∈ emb.faceBoundary f.1,
        ∃ _ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        ∃ _ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          (a : V) ∈ (e₁ : Sym2 V) ∧
            (b : V) ∈ (e₂ : Sym2 V) ∧
              BoundaryComponentWalkOnFace (emb := emb) f ∧
                ∀ g : PlanarBoundaryEdgeVertex emb,
                  g.1 ∈ emb.faceBoundary f.1 →
                    (source.toPlanarBoundaryAnnulusBoundaryData
                      |>.toBoundaryEdgeSetEdgeVertex g).1 ∉
                      cut.edgeCut.map
                        (boundaryEdgeSetInducedGraphEmbedding
                          (G := G)
                          (source.toPlanarBoundaryAnnulusBoundaryData
                            |>.ambientBoundaryEdgeSet)).mapEdgeSet

/--
All-cuts closed-walk-source cut-avoiding face-route target.  This names the
next planar foundation theorem in the form consumed by the mapped-cut
connectivity bridge.
-/
def OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) : Prop :=
  ∀ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet),
    source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget cut

/--
Cut-avoiding face routes supply mapped-cut-deleted shared-endpoint
connectivity for off-carrier attachment pairs.
-/
theorem mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget := by
  intro cut root a b hrootA hrootB
  rcases h cut root a b hrootA hrootB with
    ⟨f, e₁, e₂, he₁Face, he₂Face, he₁, he₂, ha, hb, hwalk,
      hfaceAvoid⟩
  rcases
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.exists_mappedCutAvoidingSharedEndpointGraph_reachable_of_boundaryComponentWalkOnFace
        (cut := cut) hwalk hfaceAvoid he₁Face he₂Face he₁ he₂ with
      ⟨ea, eb, hea, heb, hreachable⟩
  refine ⟨ea, eb, ?_, ?_, hreachable⟩
  · simpa [hea] using ha
  · simpa [heb] using hb

/--
Cut-avoiding face routes supply off-carrier walk consistency for the
extracted annulus boundary split.
-/
theorem offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    source.toPlanarBoundaryAnnulusBoundaryData
      |>.PeeledCollarOffCarrierWalkConsistencyTarget := by
  let data := source.toPlanarBoundaryAnnulusBoundaryData
  have hmapped :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hreachable :
      data.PeeledCollarOffCarrierCutAvoidingSharedEndpointReachabilityTarget :=
    data.cutAvoidingSharedEndpointReachabilityTarget_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      hmapped
  have hcarrier :
      data.PeeledCollarOffCarrierAttachmentCarrierConnectivityTarget :=
    data.attachmentCarrierConnectivityTarget_of_cutAvoidingSharedEndpointReachabilityTarget
      hreachable
  exact data.offCarrierWalkConsistencyTarget_of_attachmentCarrierConnectivityTarget hcarrier

/--
Cut-avoiding face routes supply the graph-facing small-cut lift for the
source's induced annulus boundary graph.
-/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.peeledCollarSmallCyclicCutLiftsToAmbient_of_offCarrierWalkConsistencyTarget
      (source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget h)

/--
The ambient minimal-counterexample regime plus cut-avoiding face routes supply
cyclic five-edge-connectivity for the source's induced annulus boundary graph.
-/
theorem cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    CyclicallyFiveEdgeConnected
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  source.toPlanarBoundaryAnnulusBoundaryData
    |>.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_offCarrierWalkConsistencyTarget
      regime
      (source.offCarrierWalkConsistencyTarget_of_mappedCutAvoidingFaceRouteTarget h)

/--
Regime-discharged S4 salvage on the source's induced annulus boundary graph,
with cyclic five-edge-connectivity supplied by cut-avoiding face routes.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph :=
  closedCollarWindingFreedomEscape_not_simplyRealizable_allSizes_of_cyclicallyFiveEdgeConnected
    (source.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
      regime h)

end PlanarBoundaryClosedWalkAnnulusBoundarySource

namespace PlanarBoundaryAnnulusCollarGeometry

/--
Canonical closed-walk-source S4 salvage from the cut-avoiding face-route
foundation target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_mappedCutAvoidingFaceRouteTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (regime :
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet)
        data.inducedBoundaryGraph)
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData)
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph := by
  have hmappedSource :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hmappedData :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget := by
    change data.boundaryData
      |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    rw [hboundary]
    exact hmappedSource
  exact
    MinimalCounterexampleCanonicalAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      regime hmappedData

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Repaired closed-walk-source S4 salvage from the cut-avoiding face-route
foundation target.
-/
theorem closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_mappedCutAvoidingFaceRouteTarget
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
    (h : source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget) :
    ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
      data.inducedBoundaryGraph := by
  have hmappedSource :
      source.toPlanarBoundaryAnnulusBoundaryData
        |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget :=
    source.mappedCutAvoidingSharedEndpointConnectivityTarget_of_mappedCutAvoidingFaceRouteTarget
      h
  have hmappedData :
      data.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget := by
    change data.toPlanarBoundaryAnnulusCollarGeometry.boundaryData
      |>.PeeledCollarOffCarrierMappedCutAvoidingSharedEndpointConnectivityTarget
    rw [hboundary]
    exact hmappedSource
  exact
    MinimalCounterexampleRepairedAnnulusPeeledCollarRouteInputs.closedCollarWindingFreedomEscape_not_simplyRealizable_of_mappedCutAvoidingSharedEndpointConnectivityTarget
      regime hmappedData

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
Closed-walk source target: cut-avoiding face routes supply cyclic
five-edge-connectivity for the source's induced annulus boundary graph.
-/
def Section92Step4ClosedWalkMappedCutAvoidingFaceRouteCyclicallyFiveEdgeConnectedTarget :
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
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget →
        CyclicallyFiveEdgeConnected
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim closed-walk cut-avoiding face-route cyclic-connectivity statement. -/
theorem section92Step4ClosedWalkMappedCutAvoidingFaceRouteCyclicallyFiveEdgeConnectedTarget :
    Section92Step4ClosedWalkMappedCutAvoidingFaceRouteCyclicallyFiveEdgeConnectedTarget := by
  intro V _ G emb source regime h
  exact
    source.cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
      regime h

/--
Closed-walk source target: regime-discharged S4 salvage with cyclic
five-edge-connectivity supplied by cut-avoiding face routes.
-/
def Section92Step4ClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
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
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph

/-- Verbatim closed-walk cut-avoiding face-route S4 statement through cyclic connectivity. -/
theorem section92Step4ClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
    Section92Step4ClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget := by
  intro V _ G emb source regime h
  exact
    source.closedCollarWindingFreedomEscape_not_simplyRealizable_of_minimalCounterexampleRegime_of_mappedCutAvoidingFaceRouteTarget
      regime h

/--
Canonical closed-walk source target: regime-discharged S4 salvage from the
cut-avoiding face-route foundation target aligned with the annulus boundary
split.
-/
def
    Section92Step4CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
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
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim canonical closed-walk cut-avoiding face-route S4 statement. -/
theorem
    section92Step4CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
    Section92Step4CanonicalAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_mappedCutAvoidingFaceRouteTarget
      regime source hboundary h

/--
Repaired closed-walk source target: regime-discharged S4 salvage from the
cut-avoiding face-route foundation target aligned with the annulus boundary
split.
-/
def
    Section92Step4RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
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
      source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget →
        ¬ ClosedCollarWindingFreedomSimplePlanarEscapeRealization
          data.inducedBoundaryGraph

/-- Verbatim repaired closed-walk cut-avoiding face-route S4 statement. -/
theorem
    section92Step4RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget :
    Section92Step4RepairedAnnulusClosedWalkMappedCutAvoidingFaceRouteRegimeDischargedS4SalvageTarget := by
  intro V _ G emb data regime source hboundary h
  exact
    data.closedCollarWindingFreedomEscape_not_simplyRealizable_of_closedWalkAnnulusBoundarySource_mappedCutAvoidingFaceRouteTarget
      regime source hboundary h

end Mettapedia.GraphTheory.FourColor
