import Mettapedia.GraphTheory.FourColor.Theorem49CollarLayerPositiveGeometry

/-!
# Lightweight closed-walk shell synthesis routes

This module keeps the live `Goal` surface on the short route from closed-walk
shell hypotheses to theorem-4.9 synthesis.  Benchmark-heavy impossibility and
regression consequences stay in the audit modules.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Repaired previous-boundary witness geometry plus a local unblocked endpoint
is enough for the live closed-walk shell synthesis route.  The closed-walk
source is retained in the statement for route traceability; the synthesis proof
only needs the induced collar-layer replacement geometry. -/
theorem theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        data.toPlanarBoundaryAnnulusCollarGeometry hEndpoint)
      C0 hC0

/-- Explicit well-founded face-peel witness data plus a local unblocked endpoint
is enough for the live closed-walk shell synthesis route.  The source argument
records that this is being consumed from a closed-walk shell. -/
theorem theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    Theorem49BoundaryRootSynthesis emb C0 := by
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49CollarLayerPositiveProjectedGeometryOn_of_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        data hEndpoint)
      C0 hC0

/-- Same-embedding parent-witness orientation from an honest closed-walk source and generic
interior-dual boundary-root adjacency-distance peel data.  This is the live shell-facing form of
the root-distance annulus construction, kept out of the heavier route/audit module. -/
theorem closedWalkShellParentWitnessOrientation_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      source.boundaryReachability interiorData).ParentWitnessOrientation :=
  parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    source.boundaryReachability interiorData

/-- Well-founded face-peel witness data on the shell's own embedding, obtained from an honest
closed-walk source and generic interior-dual boundary-root adjacency-distance peel data. -/
noncomputable def closedWalkShellWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryWellFoundedFacePeelWitnessData emb :=
  (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    source.boundaryReachability interiorData).toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness
      (closedWalkShellParentWitnessOrientation_of_interiorDualBoundaryRootAdjDistancePeelData
        source interiorData)

/-- Height-ordered face-peel witness data on the shell's own embedding, obtained by ranking the
well-founded parent witness supplied by the live shell root-distance construction. -/
noncomputable def closedWalkShellHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryHeightOrderedFacePeelWitnessData emb :=
  (closedWalkShellWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    source interiorData).toPlanarBoundaryHeightOrderedFacePeelWitnessData

end Mettapedia.GraphTheory.FourColor
