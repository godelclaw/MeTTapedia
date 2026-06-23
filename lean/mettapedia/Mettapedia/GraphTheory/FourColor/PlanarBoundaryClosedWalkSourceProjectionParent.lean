import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjectionCore
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G)
      (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
        boundaryData interiorData)
      C0 hC0 hCarrier

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C0 := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G)
      (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
        source interiorData)
      C0 hC0 hCarrier

theorem
    theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C0 x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData C0 hC0 hCarrier).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

end Mettapedia.GraphTheory.FourColor
