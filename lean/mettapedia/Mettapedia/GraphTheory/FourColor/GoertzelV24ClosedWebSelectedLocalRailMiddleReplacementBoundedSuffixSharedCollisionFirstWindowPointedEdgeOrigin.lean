import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementBoundedSuffixSharedCollisionFirstWindowPointedOrigin

/-!
# L1: localize the two pointed collision edges to the first terminal track

The pointed-origin packet identifies the successful future rail containing a
retained collision and either exposes a terminal endpoint or supplies a strict
internal occurrence.  Edge-sensitive four-cell provenance now localizes both
incident edges of every internal occurrence to the corresponding literal
track in the future's first terminal window.  The remote last-window
alternative is removed by the same source separation theorem already used at
the face level.

The terminal alternative remains explicit.  This file does not identify the
two localized edges with a square-bond endpoint triangle, construct a bypass,
prove companion-rail separation, iterate the transition, attach end caps,
construct separated crosscuts, or close the source's bulk-corridor flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

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

/-- A retained collision whose strict internal occurrence has both incident
edges localized to the correct literal first-terminal track. -/
inductive RetainedSharedCollisionFirstWindowPointedEdgeOrigin
    (future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor))
    {firstFinish secondFinish : SelectedFace (web := web)}
    (futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Prop
  | firstSecondTerminal
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support)
      (futureSecond : face ∈ futureAssembly.secondRail.support.tail)
      (futureFirstWindowSecond :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.secondSupport)
      (terminal : face = secondFinish)
  | firstSecondInterior
      (firstLive : face ∈ firstLeft.toAssembly.firstRail.support)
      (futureSecond : face ∈ futureAssembly.secondRail.support.tail)
      (futureFirstWindowSecond :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.secondSupport)
      (occurrence : InteriorOccurrence (current := face) futureAssembly.secondRail)
      (incomingEdge_firstWindow : occurrence.incomingEdge ∈
        future.transition.firstTrace.toExactTerminalWindow.secondEdges)
      (outgoingEdge_firstWindow : occurrence.outgoingEdge ∈
        future.transition.firstTrace.toExactTerminalWindow.secondEdges)
  | secondFirstTerminal
      (secondLive : face ∈ firstLeft.toAssembly.secondRail.support)
      (futureFirst : face ∈ futureAssembly.firstRail.support.tail)
      (futureFirstWindowFirst :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport)
      (terminal : face = firstFinish)
  | secondFirstInterior
      (secondLive : face ∈ firstLeft.toAssembly.secondRail.support)
      (futureFirst : face ∈ futureAssembly.firstRail.support.tail)
      (futureFirstWindowFirst :
        face ∈ future.transition.firstTrace.toExactTerminalWindow.toCertified.firstSupport)
      (occurrence : InteriorOccurrence (current := face) futureAssembly.firstRail)
      (incomingEdge_firstWindow : occurrence.incomingEdge ∈
        future.transition.firstTrace.toExactTerminalWindow.firstEdges)
      (outgoingEdge_firstWindow : occurrence.outgoingEdge ∈
        future.transition.firstTrace.toExactTerminalWindow.firstEdges)

/-- Source separation removes the remote edge-track alternative for both
incident edges of a pointed internal occurrence. -/
theorem RetainedSharedCollisionFirstWindowPointedOrigin.localizeIncidentEdges
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {future : ShiftedFuture
      (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (firstPlacement := firstPlacement)
      (secondPlacement := secondPlacement) (thirdPlacement := thirdPlacement)
      (fourthPlacement := fourthPlacement) (fifthPlacement := fifthPlacement)
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (fourthSuccessor := fourthSuccessor)}
    {firstFinish secondFinish : SelectedFace (web := web)}
    {futureAssembly : SelectedSourceLocalRailAssembly (web := web)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightAfter)
      (selectedPlacementSideFace secondPlacement firstSuccessor.frame.rightBefore)
      firstFinish secondFinish}
    {face : SelectedFace (web := web)}
    (hedges :
      EdgesContainedInOrderedExactTerminalTracks
          future.transition.firstTrace.toExactTerminalWindow
          future.transition.lastTrace.toExactTerminalWindow
          futureAssembly.firstRail.edges futureAssembly.secondRail.edges ∨
        EdgesContainedInCrossedExactTerminalTracks
          future.transition.firstTrace.toExactTerminalWindow
          future.transition.lastTrace.toExactTerminalWindow
          futureAssembly.firstRail.edges futureAssembly.secondRail.edges)
    (origin : RetainedSharedCollisionFirstWindowPointedOrigin
      (firstLeft := firstLeft) future futureAssembly face) :
    RetainedSharedCollisionFirstWindowPointedEdgeOrigin
      (firstLeft := firstLeft) future futureAssembly face := by
  cases origin with
  | firstSecond firstLive futureSecond futureFirstWindowSecond futurePosition =>
      rcases futurePosition with terminal | occurrence
      · exact .firstSecondTerminal firstLive futureSecond
          futureFirstWindowSecond terminal
      · rcases occurrence with ⟨occurrence⟩
        have localizeSecond : ∀
            (edge : Sym2 (SelectedFace (web := web))),
            edge ∈ futureAssembly.secondRail.edges → face ∈ edge →
            edge ∈ future.transition.firstTrace.toExactTerminalWindow.secondEdges := by
          intro edge hedge hface
          rcases hedges with hordered | hcrossed
          · rcases hordered.2 edge hedge with hfirst | hlast
            · exact hfirst
            · have hfaceLast :=
                future.transition.lastTrace.toExactTerminalWindow
                  |>.mem_secondSupport_of_mem_secondEdges hlast hface
              exact (firstLive_not_mem_shiftedLastWindow hsource future
                (.inl firstLive) (.inr hfaceLast)).elim
          · rcases hcrossed.2 edge hedge with hfirst | hlast
            · exact hfirst
            · have hfaceLast :=
                future.transition.lastTrace.toExactTerminalWindow
                  |>.mem_firstSupport_of_mem_firstEdges hlast hface
              exact (firstLive_not_mem_shiftedLastWindow hsource future
                (.inl firstLive) (.inl hfaceLast)).elim
        exact .firstSecondInterior firstLive futureSecond futureFirstWindowSecond
          occurrence
          (localizeSecond occurrence.incomingEdge occurrence.incomingEdge_mem_edges
            (by simp [InteriorOccurrence.incomingEdge]))
          (localizeSecond occurrence.outgoingEdge occurrence.outgoingEdge_mem_edges
            (by simp [InteriorOccurrence.outgoingEdge]))
  | secondFirst secondLive futureFirst futureFirstWindowFirst futurePosition =>
      rcases futurePosition with terminal | occurrence
      · exact .secondFirstTerminal secondLive futureFirst
          futureFirstWindowFirst terminal
      · rcases occurrence with ⟨occurrence⟩
        have localizeFirst : ∀
            (edge : Sym2 (SelectedFace (web := web))),
            edge ∈ futureAssembly.firstRail.edges → face ∈ edge →
            edge ∈ future.transition.firstTrace.toExactTerminalWindow.firstEdges := by
          intro edge hedge hface
          rcases hedges with hordered | hcrossed
          · rcases hordered.1 edge hedge with hfirst | hlast
            · exact hfirst
            · have hfaceLast :=
                future.transition.lastTrace.toExactTerminalWindow
                  |>.mem_firstSupport_of_mem_firstEdges hlast hface
              exact (firstLive_not_mem_shiftedLastWindow hsource future
                (.inr secondLive) (.inl hfaceLast)).elim
          · rcases hcrossed.1 edge hedge with hfirst | hlast
            · exact hfirst
            · have hfaceLast :=
                future.transition.lastTrace.toExactTerminalWindow
                  |>.mem_secondSupport_of_mem_secondEdges hlast hface
              exact (firstLive_not_mem_shiftedLastWindow hsource future
                (.inr secondLive) (.inr hfaceLast)).elim
        exact .secondFirstInterior secondLive futureFirst futureFirstWindowFirst
          occurrence
          (localizeFirst occurrence.incomingEdge occurrence.incomingEdge_mem_edges
            (by simp [InteriorOccurrence.incomingEdge]))
          (localizeFirst occurrence.outgoingEdge occurrence.outgoingEdge_mem_edges
            (by simp [InteriorOccurrence.outgoingEdge]))

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
