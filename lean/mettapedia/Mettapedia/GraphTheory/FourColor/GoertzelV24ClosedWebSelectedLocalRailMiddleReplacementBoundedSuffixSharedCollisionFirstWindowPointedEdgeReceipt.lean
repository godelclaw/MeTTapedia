import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailConstructionTraceEdgeReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowPointedEdgeOrigin

/-!
# L1: receipt the two pointed collision edges in the first terminal window

The first-window localization theorem places both incident edges of a strict
internal collision occurrence on one exact terminal track.  The complete
adjacent classifier now receipts every edge of either track.  Combining the
two results gives each pointed predecessor and successor edge a literal
source: an old selected forward step, a successor selected forward step, or a
named old-centre connector.

The terminal alternative remains explicit because it has no pair of internal
incident edges.  This file does not yet identify either receipted edge with a
replacement-square endpoint triangle, construct the rolling bypass, attach
end caps, construct separated crosscuts, or close Fable flag L1.
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

section TerminalWindow

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
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- Every edge on the first exact terminal track inherits the complete
adjacent classifier's literal source receipt. -/
theorem ExactSelectedLocalRailConstructionTrace.firstEdge_hasSelectedAdjacentTerminalEdgeReceipt
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    {edge : Sym2 (SelectedFace web)}
    (hedge : edge ∈ trace.toExactTerminalWindow.firstEdges) :
    SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      edge := by
  have hreceipts := trace.toOutcome_hasSelectedAdjacentTerminalEdgeReceipts
  cases hresult : trace.toOutcome with
  | straight assembly =>
      have hassembly : AssemblyHasSelectedAdjacentTerminalEdgeReceipts
          (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
          assembly := by
        simpa [SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
          hresult] using hreceipts
      apply hassembly.1 edge
      simpa [ExactSelectedLocalRailConstructionTrace.toExactTerminalWindow,
        ExactCertifiedSelectedLocalRailTerminalWindow.firstEdges, hresult] using
        hedge
  | swapped assembly =>
      have hassembly : AssemblyHasSelectedAdjacentTerminalEdgeReceipts
          (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
          assembly := by
        simpa [SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
          hresult] using hreceipts
      apply hassembly.1 edge
      simpa [ExactSelectedLocalRailConstructionTrace.toExactTerminalWindow,
        ExactCertifiedSelectedLocalRailTerminalWindow.firstEdges, hresult] using
        hedge

/-- Every edge on the second exact terminal track has the analogous literal
source receipt. -/
theorem ExactSelectedLocalRailConstructionTrace.secondEdge_hasSelectedAdjacentTerminalEdgeReceipt
    (trace : ExactSelectedLocalRailConstructionTrace successor left)
    {edge : Sym2 (SelectedFace web)}
    (hedge : edge ∈ trace.toExactTerminalWindow.secondEdges) :
    SelectedAdjacentTerminalEdgeReceipt
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      edge := by
  have hreceipts := trace.toOutcome_hasSelectedAdjacentTerminalEdgeReceipts
  cases hresult : trace.toOutcome with
  | straight assembly =>
      have hassembly : AssemblyHasSelectedAdjacentTerminalEdgeReceipts
          (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
          assembly := by
        simpa [SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
          hresult] using hreceipts
      apply hassembly.2 edge
      simpa [ExactSelectedLocalRailConstructionTrace.toExactTerminalWindow,
        ExactCertifiedSelectedLocalRailTerminalWindow.secondEdges, hresult] using
        hedge
  | swapped assembly =>
      have hassembly : AssemblyHasSelectedAdjacentTerminalEdgeReceipts
          (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
          assembly := by
        simpa [SelectedLocalRailAppendCompleteOutcome.HasSelectedAdjacentTerminalEdgeReceipts,
          hresult] using hreceipts
      apply hassembly.2 edge
      simpa [ExactSelectedLocalRailConstructionTrace.toExactTerminalWindow,
        ExactCertifiedSelectedLocalRailTerminalWindow.secondEdges, hresult] using
        hedge

end TerminalWindow

section PointedCollision

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

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

/-- In the first-to-second internal alternative, both incident edges lie on
the second first-window track and therefore receive literal source receipts.
The arguments are exactly the proof fields carried by
`firstSecondInterior`; no terminal case is coerced into this statement. -/
theorem firstSecondInterior_hasIncidentEdgeReceipts
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace web}
    {firstFinish secondFinish : SelectedFace web}
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
    SelectedAdjacentTerminalEdgeReceipt
        (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
        occurrence.incomingEdge ∧
      SelectedAdjacentTerminalEdgeReceipt
        (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
        occurrence.outgoingEdge :=
  ⟨future.transition.firstTrace
      |>.secondEdge_hasSelectedAdjacentTerminalEdgeReceipt
        incomingEdge_firstWindow,
    future.transition.firstTrace
      |>.secondEdge_hasSelectedAdjacentTerminalEdgeReceipt
        outgoingEdge_firstWindow⟩

/-- The second-to-first internal alternative is the symmetric second-track
projection. -/
theorem secondFirstInterior_hasIncidentEdgeReceipts
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {face : SelectedFace web}
    {firstFinish secondFinish : SelectedFace web}
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
    SelectedAdjacentTerminalEdgeReceipt
        (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
        occurrence.incomingEdge ∧
      SelectedAdjacentTerminalEdgeReceipt
        (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
        occurrence.outgoingEdge :=
  ⟨future.transition.firstTrace
      |>.firstEdge_hasSelectedAdjacentTerminalEdgeReceipt
        incomingEdge_firstWindow,
    future.transition.firstTrace
      |>.firstEdge_hasSelectedAdjacentTerminalEdgeReceipt
        outgoingEdge_firstWindow⟩

end PointedCollision

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
