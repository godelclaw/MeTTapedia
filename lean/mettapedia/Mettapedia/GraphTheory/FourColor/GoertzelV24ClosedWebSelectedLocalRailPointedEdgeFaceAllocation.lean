import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeTriangleComparison

/-!
# L1: allocate pointed rail endpoints to exact source faces

The pointed-collision layer retains the incoming and outgoing unoriented dual
edges.  The source crossing-origin packet retains the two literal faces of
each such edge.  Equality of unordered pairs therefore gives an exact
orientation-free allocation: the predecessor and collision face are those
two source faces in one order, and the collision face and successor are those
two source faces in one order.

This is the finite face-coordinate input for locating the two pointed edges
at collision-adjacent steps of a replacement square.  It does not choose an
orientation, identify a source corner with a square-bond endpoint, consume the
opposite-endpoint alternative, construct a rolling bypass, attach end caps,
construct separated crosscuts, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- The predecessor and collision face of a pointed occurrence are exactly
the two source faces retained by the incoming crossing origin, with the only
ambiguity being the orientation of the unoriented dual edge. -/
theorem InteriorOccurrence.incoming_faces_eq_of_crossingOrigin
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.incomingEdge) :
    (occurrence.predecessor = origin.toCrossingReceipt.first ∧
        current = origin.toCrossingReceipt.second) ∨
      (occurrence.predecessor = origin.toCrossingReceipt.second ∧
        current = origin.toCrossingReceipt.first) := by
  apply Sym2.eq_iff.mp
  simpa [InteriorOccurrence.incomingEdge] using
    origin.toCrossingReceipt.edge_eq

/-- The collision face and successor of a pointed occurrence are exactly the
two source faces retained by the outgoing crossing origin, again modulo only
the orientation of the unoriented dual edge. -/
theorem InteriorOccurrence.outgoing_faces_eq_of_crossingOrigin
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.outgoingEdge) :
    (current = origin.toCrossingReceipt.first ∧
        occurrence.successor = origin.toCrossingReceipt.second) ∨
      (current = origin.toCrossingReceipt.second ∧
        occurrence.successor = origin.toCrossingReceipt.first) := by
  apply Sym2.eq_iff.mp
  simpa [InteriorOccurrence.outgoingEdge] using
    origin.toCrossingReceipt.edge_eq

/-- Both pointed rail edges retain their exact source-face allocations.  This
joint packet is the direct input expected by the collision-adjacent square
step comparison; it adds no geometric hypothesis. -/
theorem InteriorOccurrence.pointed_faces_eq_of_crossingOrigins
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (incomingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.incomingEdge)
    (outgoingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.outgoingEdge) :
    ((occurrence.predecessor = incomingOrigin.toCrossingReceipt.first ∧
          current = incomingOrigin.toCrossingReceipt.second) ∨
        (occurrence.predecessor = incomingOrigin.toCrossingReceipt.second ∧
          current = incomingOrigin.toCrossingReceipt.first)) ∧
      ((current = outgoingOrigin.toCrossingReceipt.first ∧
          occurrence.successor = outgoingOrigin.toCrossingReceipt.second) ∨
        (current = outgoingOrigin.toCrossingReceipt.second ∧
          occurrence.successor = outgoingOrigin.toCrossingReceipt.first)) :=
  ⟨InteriorOccurrence.incoming_faces_eq_of_crossingOrigin
      occurrence incomingOrigin,
    InteriorOccurrence.outgoing_faces_eq_of_crossingOrigin
      occurrence outgoingOrigin⟩

/-- The complete proof-relevant source-face allocation of the two incident
edges at one strict pointed collision.  The origins preserve the selected
Cell--3 corner and primal crossing; the two allocation fields preserve the
literal predecessor/current/successor faces. -/
structure InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk) where
  incomingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    occurrence.incomingEdge
  outgoingOrigin : SelectedAdjacentTerminalEdgeCrossingOrigin
    (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
    occurrence.outgoingEdge
  incomingFaces :
    (occurrence.predecessor = incomingOrigin.toCrossingReceipt.first ∧
        current = incomingOrigin.toCrossingReceipt.second) ∨
      (occurrence.predecessor = incomingOrigin.toCrossingReceipt.second ∧
        current = incomingOrigin.toCrossingReceipt.first)
  outgoingFaces :
    (current = outgoingOrigin.toCrossingReceipt.first ∧
        occurrence.successor = outgoingOrigin.toCrossingReceipt.second) ∨
      (current = outgoingOrigin.toCrossingReceipt.second ∧
        occurrence.successor = outgoingOrigin.toCrossingReceipt.first)

/-- Two literal terminal-edge receipts construct the complete pointed
source-face allocation.  In particular, no later square consumer needs to
choose or assume crossing provenance for either rail edge. -/
theorem InteriorOccurrence.exists_selectedAdjacentPointedFaceAllocation
    {start finish current : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) walk)
    (incomingReceipt : SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.incomingEdge)
    (outgoingReceipt : SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence.outgoingEdge) :
    Nonempty (InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      occurrence) := by
  rcases incomingReceipt.toCrossingOrigin with ⟨incomingOrigin⟩
  rcases outgoingReceipt.toCrossingOrigin with ⟨outgoingOrigin⟩
  exact ⟨{
    incomingOrigin := incomingOrigin
    outgoingOrigin := outgoingOrigin
    incomingFaces :=
      InteriorOccurrence.incoming_faces_eq_of_crossingOrigin
        occurrence incomingOrigin
    outgoingFaces :=
      InteriorOccurrence.outgoing_faces_eq_of_crossingOrigin
        occurrence outgoingOrigin
  }⟩

section FirstWindowCollision

variable
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {hfourthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center.val + 2 < blockLength}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {fifthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext)
        hfourthNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {fourthSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfourthNext
      fourthPlacement fifthPlacement}

private abbrev ShiftedFuture :=
  SupportCertifiedExactSelectedLocalRailTracedFourCellTransition
    (firstInterior := nextCorridorInterior firstInterior hfirstNext)
    (hfirstNext := hbridgeNext) (hbridgeNext := hlastNext)
    (hlastNext := hfourthNext)
    (firstPlacement := secondPlacement) (secondPlacement := thirdPlacement)
    (thirdPlacement := fourthPlacement) (fourthPlacement := fifthPlacement)
    (firstSuccessor := bridge) (bridge := lastSuccessor)
    (lastSuccessor := fourthSuccessor)
    (firstLeft := firstSuccessor.rightRailsAsNextLeft bridge)

/-- The literal first-to-second strict collision alternative carries the
complete pointed source-face allocation.  This connects the generic packet
above to the actual first terminal window; it adds no hypothesis. -/
theorem firstSecondInterior_hasPointedFaceAllocation
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face firstFinish secondFinish : SelectedFace web}
    {futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    (occurrence : InteriorOccurrence (current := face)
      futureAssembly.secondRail)
    (incomingEdge_firstWindow : occurrence.incomingEdge ∈
      future.transition.firstTrace.toExactTerminalWindow.secondEdges)
    (outgoingEdge_firstWindow : occurrence.outgoingEdge ∈
      future.transition.firstTrace.toExactTerminalWindow.secondEdges) :
    Nonempty (InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence) := by
  rcases firstSecondInterior_hasIncidentEdgeReceipts
      occurrence incomingEdge_firstWindow
      outgoingEdge_firstWindow with ⟨incomingReceipt, outgoingReceipt⟩
  exact InteriorOccurrence.exists_selectedAdjacentPointedFaceAllocation
    occurrence incomingReceipt outgoingReceipt

/-- The symmetric second-to-first strict collision alternative carries the
same complete pointed source-face allocation on the first terminal track. -/
theorem secondFirstInterior_hasPointedFaceAllocation
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face firstFinish secondFinish : SelectedFace web}
    {futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    (occurrence : InteriorOccurrence (current := face)
      futureAssembly.firstRail)
    (incomingEdge_firstWindow : occurrence.incomingEdge ∈
      future.transition.firstTrace.toExactTerminalWindow.firstEdges)
    (outgoingEdge_firstWindow : occurrence.outgoingEdge ∈
      future.transition.firstTrace.toExactTerminalWindow.firstEdges) :
    Nonempty (InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence) := by
  rcases secondFirstInterior_hasIncidentEdgeReceipts
      occurrence incomingEdge_firstWindow
      outgoingEdge_firstWindow with ⟨incomingReceipt, outgoingReceipt⟩
  exact InteriorOccurrence.exists_selectedAdjacentPointedFaceAllocation
    occurrence incomingReceipt outgoingReceipt

end FirstWindowCollision

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
