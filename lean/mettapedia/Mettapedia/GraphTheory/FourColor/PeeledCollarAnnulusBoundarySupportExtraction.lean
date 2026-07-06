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
The same selected ambient boundary edge, viewed as a vertex of the canonical
finite edge carrier attached to the annulus boundary split.
-/
def toBoundaryEdgeSetEdgeVertex
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (e : PlanarBoundaryEdgeVertex emb) :
    BoundaryEdgeSetEdgeVertex (G := G) data.ambientBoundaryEdgeSet :=
  ⟨e.1, by
    rw [data.ambientBoundaryEdgeSet_eq_selectedBoundarySupport]
    exact e.2⟩

@[simp]
theorem toBoundaryEdgeSetEdgeVertex_val
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    (e : PlanarBoundaryEdgeVertex emb) :
    (data.toBoundaryEdgeSetEdgeVertex e).1 = e.1 :=
  rfl

/--
Endpoint-sharing adjacency in the selected-boundary support graph is the same
adjacency after the annulus boundary split is reindexed as its canonical finite
edge carrier.
-/
theorem
    boundaryEdgeSetSharedEndpointGraph_adj_of_planarBoundarySupportEndpointAdjGraph_adj
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {e f : PlanarBoundaryEdgeVertex emb}
    (h :
      (planarBoundarySupportEndpointAdjGraph emb).Adj e f) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Adj
      (data.toBoundaryEdgeSetEdgeVertex e)
      (data.toBoundaryEdgeSetEdgeVertex f) := by
  rcases h with ⟨hne, v, hvE, hvF⟩
  refine ⟨?_, v, hvE, hvF⟩
  intro hEq
  apply hne
  apply Subtype.ext
  exact congrArg
    (fun x : BoundaryEdgeSetEdgeVertex (G := G) data.ambientBoundaryEdgeSet => x.1)
    hEq

/--
Walks in the selected-boundary support graph transport to walks in the
canonical finite annulus boundary edge carrier.
-/
theorem
    exists_boundaryEdgeSetSharedEndpointGraph_walk_of_planarBoundarySupportEndpointAdjGraph_walk
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {e f : PlanarBoundaryEdgeVertex emb}
    (p : (planarBoundarySupportEndpointAdjGraph emb).Walk e f) :
    ∃ _ : (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Walk
        (data.toBoundaryEdgeSetEdgeVertex e)
        (data.toBoundaryEdgeSetEdgeVertex f),
      True := by
  induction p with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil, trivial⟩
  | @cons e₀ e₁ e₂ hadj p ih =>
      rcases ih with ⟨q, _⟩
      exact
        ⟨SimpleGraph.Walk.cons
          (data.boundaryEdgeSetSharedEndpointGraph_adj_of_planarBoundarySupportEndpointAdjGraph_adj
            hadj)
          q,
        trivial⟩

/--
Reachability in the selected-boundary support graph transports to reachability
in the canonical finite annulus boundary edge carrier.
-/
theorem
    boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {e f : PlanarBoundaryEdgeVertex emb}
    (h :
      (planarBoundarySupportEndpointAdjGraph emb).Reachable e f) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.toBoundaryEdgeSetEdgeVertex e)
      (data.toBoundaryEdgeSetEdgeVertex f) := by
  rcases h with ⟨p⟩
  rcases
    data.exists_boundaryEdgeSetSharedEndpointGraph_walk_of_planarBoundarySupportEndpointAdjGraph_walk
      p with
    ⟨q, _⟩
  exact ⟨q⟩

/--
Facewise selected-boundary component reachability, stated in the planar
embedding API, supplies carrier reachability for the corresponding annulus
boundary-edge vertices.
-/
theorem boundaryEdgeSetSharedEndpointGraph_reachable_of_boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryData emb)
    {f : AmbientFace emb.faces}
    (hface : BoundaryComponentReachableOnFace (emb := emb) f)
    {e₁ e₂ : G.edgeSet}
    (he₁Face : e₁ ∈ emb.faceBoundary f.1)
    (he₂Face : e₂ ∈ emb.faceBoundary f.1)
    (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.toBoundaryEdgeSetEdgeVertex ⟨e₁, he₁⟩)
      (data.toBoundaryEdgeSetEdgeVertex ⟨e₂, he₂⟩) :=
  data.boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable
    (hface he₁Face he₂Face he₁ he₂)

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

/--
Reachability in the selected-boundary support graph transports to reachability
in the annulus collar geometry's canonical finite boundary edge carrier.
-/
theorem
    boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    {e f : PlanarBoundaryEdgeVertex emb}
    (h :
      (planarBoundarySupportEndpointAdjGraph emb).Reachable e f) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.boundaryData.toBoundaryEdgeSetEdgeVertex e)
      (data.boundaryData.toBoundaryEdgeSetEdgeVertex f) :=
  data.boundaryData
    |>.boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable h

/--
Facewise selected-boundary component reachability supplies carrier reachability
for an annulus collar geometry's canonical boundary-edge vertices.
-/
theorem boundaryEdgeSetSharedEndpointGraph_reachable_of_boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    {f : AmbientFace emb.faces}
    (hface : BoundaryComponentReachableOnFace (emb := emb) f)
    {e₁ e₂ : G.edgeSet}
    (he₁Face : e₁ ∈ emb.faceBoundary f.1)
    (he₂Face : e₂ ∈ emb.faceBoundary f.1)
    (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.boundaryData.toBoundaryEdgeSetEdgeVertex ⟨e₁, he₁⟩)
      (data.boundaryData.toBoundaryEdgeSetEdgeVertex ⟨e₂, he₂⟩) :=
  data.boundaryData.boundaryEdgeSetSharedEndpointGraph_reachable_of_boundaryComponentReachableOnFace
    hface he₁Face he₂Face he₁ he₂

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

/--
Reachability in the selected-boundary support graph transports to reachability
in a repaired annulus geometry's canonical finite boundary edge carrier.
-/
theorem
    boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {e f : PlanarBoundaryEdgeVertex emb}
    (h :
      (planarBoundarySupportEndpointAdjGraph emb).Reachable e f) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.boundaryData.toBoundaryEdgeSetEdgeVertex e)
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.boundaryData.toBoundaryEdgeSetEdgeVertex f) :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.boundaryEdgeSetSharedEndpointGraph_reachable_of_planarBoundarySupportEndpointAdjGraph_reachable
      h

/--
Facewise selected-boundary component reachability supplies carrier reachability
for a repaired annulus geometry's canonical boundary-edge vertices.
-/
theorem boundaryEdgeSetSharedEndpointGraph_reachable_of_boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {f : AmbientFace emb.faces}
    (hface : BoundaryComponentReachableOnFace (emb := emb) f)
    {e₁ e₂ : G.edgeSet}
    (he₁Face : e₁ ∈ emb.faceBoundary f.1)
    (he₂Face : e₂ ∈ emb.faceBoundary f.1)
    (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    (BoundaryEdgeSetSharedEndpointGraph
        (G := G) data.ambientBoundaryEdgeSet).Reachable
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.boundaryData.toBoundaryEdgeSetEdgeVertex ⟨e₁, he₁⟩)
      (data.toPlanarBoundaryAnnulusCollarGeometry
        |>.boundaryData.toBoundaryEdgeSetEdgeVertex ⟨e₂, he₂⟩) :=
  data.toPlanarBoundaryAnnulusCollarGeometry
    |>.boundaryEdgeSetSharedEndpointGraph_reachable_of_boundaryComponentReachableOnFace
      hface he₁Face he₂Face he₁ he₂

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

end Mettapedia.GraphTheory.FourColor
