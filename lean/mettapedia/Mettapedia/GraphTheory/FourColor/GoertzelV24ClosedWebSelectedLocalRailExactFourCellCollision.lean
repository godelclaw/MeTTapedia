import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailExactTerminalWindow
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailFourCellCollision

/-!
# L1: exact source-piece location of a four-cell rail collision

The coarse four-centre classifier places a failed append in five dual-geometric
positions.  Its terminal windows now retain a second, independent coordinate:
the literal Cell-3 pieces supporting each rail.  This module exposes that
coordinate for both windows and combines it with the five-case classification.

No collision is removed here.  The result is the finite product consumed by
the next direct repair; it does not iterate a rail chain, attach an end cap, or
close Fable flag L1.
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- Every face of the first exact terminal support retains literal five-piece
source provenance. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.firstSupport_in_adjacentPieces
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left) :
    ∀ face ∈ window.toCertified.firstSupport,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly => exact hexact.1
  | swapped assembly => exact hexact.1

/-- The second exact terminal support has the same literal provenance. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.secondSupport_in_adjacentPieces
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left) :
    ∀ face ∈ window.toCertified.secondSupport,
      FaceInAdjacentSelectedRailPieces (successor := successor)
        (left := left) face := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly => exact hexact.2
  | swapped assembly => exact hexact.2

variable
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

private abbrev LastLeft :=
  bridge.rightRailsAsNextLeft lastSuccessor

/-- An ordered collision between exact windows belongs to literal source
pieces in both windows. -/
theorem orderedExactFourCellCollision_face_in_both_piece_envelopes
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.toCertified.firstSupport firstWindow.toCertified.secondSupport
      lastWindow.toCertified.firstSupport lastWindow.toCertified.secondSupport) :
    FaceInAdjacentSelectedRailPieces (successor := firstSuccessor)
        (left := firstLeft) collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := lastSuccessor)
        (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
        collision.face := by
  constructor
  · rcases collision.face_mem_old with hfirst | hsecond
    · exact firstWindow.firstSupport_in_adjacentPieces collision.face hfirst
    · exact firstWindow.secondSupport_in_adjacentPieces collision.face hsecond
  · rcases collision.face_mem_new with hfirst | hsecond
    · exact lastWindow.firstSupport_in_adjacentPieces collision.face hfirst
    · exact lastWindow.secondSupport_in_adjacentPieces collision.face hsecond

/-- Crossed endpoint order changes only which new rail is compared; exact
piece provenance is unchanged. -/
theorem crossedExactFourCellCollision_face_in_both_piece_envelopes
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.toCertified.firstSupport firstWindow.toCertified.secondSupport
      lastWindow.toCertified.secondSupport lastWindow.toCertified.firstSupport) :
    FaceInAdjacentSelectedRailPieces (successor := firstSuccessor)
        (left := firstLeft) collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := lastSuccessor)
        (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
        collision.face := by
  constructor
  · rcases collision.face_mem_old with hfirst | hsecond
    · exact firstWindow.firstSupport_in_adjacentPieces collision.face hfirst
    · exact firstWindow.secondSupport_in_adjacentPieces collision.face hsecond
  · rcases collision.face_mem_new with hsecond | hfirst
    · exact lastWindow.secondSupport_in_adjacentPieces collision.face hsecond
    · exact lastWindow.firstSupport_in_adjacentPieces collision.face hfirst

/-- Ordered exact collisions carry both independent finite coordinates: the
five dual-geometric cases and the two literal piece envelopes. -/
theorem orderedExactFourCellCollision_geometry_and_pieces
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.toCertified.firstSupport firstWindow.toCertified.secondSupport
      lastWindow.toCertified.firstSupport lastWindow.toCertified.secondSupport) :
    FourCenterCollisionGeometry (corridor := corridor)
        firstInterior.center
        (nextCorridorInterior firstInterior hfirstNext).center
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := firstSuccessor)
        (left := firstLeft) collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := lastSuccessor)
        (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
        collision.face := by
  exact ⟨orderedFourCellCollision_geometry hsource firstWindow.toCertified
      lastWindow.toCertified collision,
    orderedExactFourCellCollision_face_in_both_piece_envelopes
      firstWindow lastWindow collision⟩

/-- The same exact product classification in crossed endpoint order. -/
theorem crossedExactFourCellCollision_geometry_and_pieces
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (firstWindow : ExactCertifiedSelectedLocalRailTerminalWindow
      firstSuccessor firstLeft)
    (lastWindow : ExactCertifiedSelectedLocalRailTerminalWindow lastSuccessor
      (LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor)))
    (collision : SelectedRailPairAppendCollision (web := web)
      firstWindow.toCertified.firstSupport firstWindow.toCertified.secondSupport
      lastWindow.toCertified.secondSupport lastWindow.toCertified.firstSupport) :
    FourCenterCollisionGeometry (corridor := corridor)
        firstInterior.center
        (nextCorridorInterior firstInterior hfirstNext).center
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := firstSuccessor)
        (left := firstLeft) collision.face ∧
      FaceInAdjacentSelectedRailPieces (successor := lastSuccessor)
        (left := LastLeft (bridge := bridge) (lastSuccessor := lastSuccessor))
        collision.face := by
  exact ⟨crossedFourCellCollision_geometry hsource firstWindow.toCertified
      lastWindow.toCertified collision,
    crossedExactFourCellCollision_face_in_both_piece_envelopes
      firstWindow lastWindow collision⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
