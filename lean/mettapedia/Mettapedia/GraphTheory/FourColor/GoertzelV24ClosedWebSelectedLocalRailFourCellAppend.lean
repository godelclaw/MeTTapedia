import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairAppendClassification

/-!
# L1: classify the append of two literal two-cell rail windows

Four consecutive selected Cell-3 placements provide two certified two-cell
windows separated by one canonical successor seam.  Consecutive-frame
compatibility rebases the second window at the first window's endpoints, and
the generic four-way support classifier then either constructs the complete
four-cell assembly or returns the exact failed interaction.

Straight/swapped endpoint order is composed rather than erased.  This is the
source-facing finite transition alternative for two windows.  It does not yet
repair its collision branch, prove successor existence through every local
collision alternative, iterate to arbitrary length, attach either annular end
cap, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
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
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- The complete four-cell output, or the exact failed interaction after the
second window is placed in the order required by the first. -/
inductive CertifiedSelectedLocalRailFourCellAppendOutcome
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        (selectedPlacementSideFace firstPlacement firstIncomingBefore)
        (selectedPlacementSideFace firstPlacement firstIncomingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingAfter)
        (selectedPlacementSideFace fourthPlacement
          lastSuccessor.rightOutgoingBefore))
  | orderedCollision
      (witness : SelectedRailPairAppendCollision (web := web)
        firstWindow.firstSupport firstWindow.secondSupport
        lastWindow.firstSupport lastWindow.secondSupport)
  | crossedCollision
      (witness : SelectedRailPairAppendCollision (web := web)
        firstWindow.firstSupport firstWindow.secondSupport
        lastWindow.secondSupport lastWindow.firstSupport)

/-- An ordered four-cell collision is literally confined to both certified
two-centre windows.  This turns the remaining repair into a bounded local
intersection problem. -/
theorem orderedFourCellCollision_face_near_both_windows
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.firstSupport firstWindow.secondSupport
      lastWindow.firstSupport lastWindow.secondSupport) :
    FaceNearSelectedCenterPair (corridor := corridor)
        firstInterior.center
        (nextCorridorInterior firstInterior hfirstNext).center collision.face ∧
      FaceNearSelectedCenterPair (corridor := corridor)
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center collision.face := by
  constructor
  · rcases collision.face_mem_old with hfirst | hsecond
    · exact firstWindow.firstSupport_near collision.face hfirst
    · exact firstWindow.secondSupport_near collision.face hsecond
  · rcases collision.face_mem_new with hfirst | hsecond
    · exact lastWindow.firstSupport_near collision.face hfirst
    · exact lastWindow.secondSupport_near collision.face hsecond

/-- The same bounded-location certificate when the second window is followed
in crossed endpoint order. -/
theorem crossedFourCellCollision_face_near_both_windows
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.firstSupport firstWindow.secondSupport
      lastWindow.secondSupport lastWindow.firstSupport) :
    FaceNearSelectedCenterPair (corridor := corridor)
        firstInterior.center
        (nextCorridorInterior firstInterior hfirstNext).center collision.face ∧
      FaceNearSelectedCenterPair (corridor := corridor)
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center collision.face := by
  constructor
  · rcases collision.face_mem_old with hfirst | hsecond
    · exact firstWindow.firstSupport_near collision.face hfirst
    · exact firstWindow.secondSupport_near collision.face hsecond
  · rcases collision.face_mem_new with hsecond | hfirst
    · exact lastWindow.secondSupport_near collision.face hsecond
    · exact lastWindow.firstSupport_near collision.face hfirst

/-- **L1 four-cell transition alternative.** Rebase and classify two literal
certified two-cell windows.  Endpoint order composes by parity; every failed
append returns its actual common face. -/
noncomputable def classifyCertifiedSelectedLocalRailFourCellAppend
    (firstWindow : CertifiedSelectedLocalRailTerminalWindow firstSuccessor firstLeft)
    (lastWindow : CertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))) :
    CertifiedSelectedLocalRailFourCellAppendOutcome firstWindow lastWindow :=
  match hfirst : firstWindow.outcome with
  | .straight firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppend firstAssembly rebased with
          | .assembled assembly => .straight assembly
          | .collision witness => .orderedCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
      | .swapped lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppend firstAssembly rebased with
          | .assembled assembly => .swapped assembly
          | .collision witness => .orderedCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
  | .swapped firstAssembly =>
      match hlast : lastWindow.outcome with
      | .straight lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendCrossed firstAssembly rebased with
          | .assembled assembly => .swapped assembly
          | .collision witness => .crossedCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)
      | .swapped lastAssembly =>
          let rebased := rebaseAssemblyStart lastAssembly
            (firstSuccessor.rightOutgoingBeforeFace_eq_nextRightAfterFace bridge).symm
            (firstSuccessor.rightOutgoingAfterFace_eq_nextRightBeforeFace bridge).symm
          match classifyAndAppendCrossed firstAssembly rebased with
          | .assembled assembly => .straight assembly
          | .collision witness => .crossedCollision (by
              have hfirstSupport : rebased.firstRail.support =
                  lastAssembly.firstRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_firstRail_support
              have hsecondSupport : rebased.secondRail.support =
                  lastAssembly.secondRail.support := by
                dsimp [rebased]
                apply rebaseAssemblyStart_secondRail_support
              rw [hfirstSupport, hsecondSupport] at witness
              simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
                CertifiedSelectedLocalRailTerminalWindow.secondSupport,
                hfirst, hlast] using witness)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
