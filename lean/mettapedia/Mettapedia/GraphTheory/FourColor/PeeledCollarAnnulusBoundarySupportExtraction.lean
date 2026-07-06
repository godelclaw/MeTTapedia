import Mettapedia.GraphTheory.FourColor.PeeledCollarBoundarySupportExtraction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

namespace PlanarBoundaryAnnulusBoundaryData

/--
The finite ambient edge set selected by an annulus boundary split.
-/
abbrev ambientBoundaryEdgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) : Finset G.edgeSet :=
  data.outerAmbientBoundary ∪ data.innerAmbientBoundary

/--
The canonical graph induced on the endpoint support of the selected annulus
boundary edge set.
-/
abbrev inducedBoundaryGraph
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    SimpleGraph
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet) :=
  BoundaryEdgeSetInducedGraph (G := G) data.ambientBoundaryEdgeSet

/--
The natural embedding of the canonical annulus-boundary induced graph into the
ambient graph.
-/
abbrev inducedBoundaryEmbedding
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    data.inducedBoundaryGraph ↪g G :=
  boundaryEdgeSetInducedGraphEmbedding (G := G) data.ambientBoundaryEdgeSet

/--
The annulus boundary edge set is exactly the selected boundary support of the
ambient boundary-aware embedding.
-/
theorem ambientBoundaryEdgeSet_eq_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb) :
    data.ambientBoundaryEdgeSet =
      selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
  data.ambientBoundary_eq.symm

/--
Selected-boundary inducedness identifies the canonical annulus-boundary
induced graph with the selected finite boundary edge set, in edge-image form.
-/
theorem inducedBoundaryGraphRepresents_of_selectedBoundaryInducedSubgraph
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (hSelected : SelectedBoundaryInducedSubgraph emb) :
    BoundaryEdgeSetInducedGraphRepresents (G := G) data.ambientBoundaryEdgeSet := by
  apply boundaryEdgeSetInducedGraph_represents_of_inducedSubgraph
  simpa [SelectedBoundaryInducedSubgraph,
    PlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet, data.ambientBoundary_eq] using
    hSelected

/--
Outer/inner inducedness plus cross-component chord-freeness identify the
canonical annulus-boundary induced graph with the selected finite boundary edge
set, in edge-image form.
-/
theorem
    inducedBoundaryGraphRepresents_of_inducedBoundaryComponents_of_crossComponentChordFree
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary) :
    BoundaryEdgeSetInducedGraphRepresents (G := G) data.ambientBoundaryEdgeSet :=
  data.inducedBoundaryGraphRepresents_of_selectedBoundaryInducedSubgraph
    (data.selectedBoundaryInducedSubgraph_of_inducedBoundaryComponents_of_crossComponentChordFree
      hOuter hInner hCross)

end PlanarBoundaryAnnulusBoundaryData

namespace PlanarBoundaryAnnulusCollarGeometry

/--
The boundary-data component of an annulus collar geometry.
-/
abbrev boundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryAnnulusBoundaryData emb :=
  data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData

/--
The finite ambient edge set selected by an annulus collar geometry's ambient
boundary split.
-/
abbrev ambientBoundaryEdgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) : Finset G.edgeSet :=
  data.boundaryData.ambientBoundaryEdgeSet

/--
The canonical graph induced on the endpoint support of an annulus collar
geometry's selected ambient boundary edge set.
-/
abbrev inducedBoundaryGraph
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    SimpleGraph
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet) :=
  data.boundaryData.inducedBoundaryGraph

/--
The natural embedding of the annulus collar geometry's canonical boundary graph
into the ambient graph.
-/
abbrev inducedBoundaryEmbedding
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    data.inducedBoundaryGraph ↪g G :=
  data.boundaryData.inducedBoundaryEmbedding

/--
Outer/inner inducedness plus cross-component chord-freeness identify the
annulus collar geometry's canonical boundary induced graph with its selected
finite ambient boundary edge set, in edge-image form.
-/
theorem
    inducedBoundaryGraphRepresents_of_inducedBoundaryComponents_of_crossComponentChordFree
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary) :
    BoundaryEdgeSetInducedGraphRepresents (G := G) data.ambientBoundaryEdgeSet :=
  data.boundaryData.inducedBoundaryGraphRepresents_of_inducedBoundaryComponents_of_crossComponentChordFree
    hOuter hInner hCross

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
The finite ambient edge set selected by a repaired annulus geometry's ambient
boundary split.
-/
abbrev ambientBoundaryEdgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Finset G.edgeSet :=
  data.toPlanarBoundaryAnnulusCollarGeometry.ambientBoundaryEdgeSet

/--
The canonical graph induced on the endpoint support of a repaired annulus
geometry's selected ambient boundary edge set.
-/
abbrev inducedBoundaryGraph
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    SimpleGraph
      (BoundaryEdgeSetEndpointVertex (G := G) data.ambientBoundaryEdgeSet) :=
  data.toPlanarBoundaryAnnulusCollarGeometry.inducedBoundaryGraph

/--
The natural embedding of the repaired annulus geometry's canonical boundary
graph into the ambient graph.
-/
abbrev inducedBoundaryEmbedding
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    data.inducedBoundaryGraph ↪g G :=
  data.toPlanarBoundaryAnnulusCollarGeometry.inducedBoundaryEmbedding

/--
Outer/inner inducedness plus cross-component chord-freeness identify the
repaired annulus geometry's canonical boundary induced graph with its selected
finite ambient boundary edge set, in edge-image form.
-/
theorem
    inducedBoundaryGraphRepresents_of_inducedBoundaryComponents_of_crossComponentChordFree
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hOuter : BoundaryEdgeSetInducedSubgraph data.outerAmbientBoundary)
    (hInner : BoundaryEdgeSetInducedSubgraph data.innerAmbientBoundary)
    (hCross :
      BoundaryEdgeSetCrossComponentChordFree
        data.outerAmbientBoundary data.innerAmbientBoundary) :
    BoundaryEdgeSetInducedGraphRepresents (G := G) data.ambientBoundaryEdgeSet :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.inducedBoundaryGraphRepresents_of_inducedBoundaryComponents_of_crossComponentChordFree
      hOuter hInner hCross

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

end Mettapedia.GraphTheory.FourColor
