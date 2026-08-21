import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeCenterCoordinate
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeOldForwardSquareChord

/-!
# L1: reduce the source-square pointed-origin table

Once an old-forward origin has been converted into the literal diagonal of
the canonical first--third square, only four pairs of incident source origins
appear possible.  The old-centre/old-centre pair is already excluded by
simplicity of the pointed rail.  Thus the non-chord branch has exactly three
remaining rows: successor/successor, successor/old-centre, and
old-centre/successor.

This is finite local classification supporting L1.  It neither consumes the
square chord nor proves companion separation, rolling iteration, end caps,
the separated-crosscut constructor, or L1.
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
    {web : Instance data coloring}
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}

/-- Whether an adjacent-terminal crossing origin comes from a forward step in
the successor selected placement. -/
def SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {dualEdge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      dualEdge) : Prop :=
  match origin with
  | .successorForward _ _ _ _ => True
  | .oldForward _ _ _ _ | .oldCenter _ _ => False

/-- Whether an adjacent-terminal crossing origin is an explicit connector
from the older selected placement's centre. -/
def SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {dualEdge : Sym2 (SelectedFace web)}
    (origin : SelectedAdjacentTerminalEdgeCrossingOrigin
      (leftPlacement := leftPlacement) (rightPlacement := rightPlacement)
      dualEdge) : Prop :=
  match origin with
  | .oldCenter _ _ => True
  | .oldForward _ _ _ _ | .successorForward _ _ _ _ => False

/-- **L1 source-square origin reduction.**  At a simple pointed collision on
the canonical first--third square, either the old-forward square diagonal is
exhibited or the incident origins lie in exactly one of the three remaining
successor/old-centre rows. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.sourceSquare_isChord_or_three_origin_rows
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hpath : walk.IsPath)
    (hfirst : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    let square := squareDualCycle_of_firstThirdSquare
      (rungs := rungs) hfirst hthird hfaceSecond
    square.cycle.walk.IsChord
        s(corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
            (nextCorridorInterior firstInterior hfirstNext).center,
          face) ∨
      ((allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsSuccessorForward) ∨
        (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsOldCenter) ∨
        (allocation.incomingOrigin.IsOldCenter ∧
          allocation.outgoingOrigin.IsSuccessorForward)) := by
  dsimp only
  rcases allocation.sourceSquare_isChord_or_incidentOrigins_notOldForward
      hfirst hthird hfaceSecond with hchord | hnotOld
  · exact .inl hchord
  · right
    generalize hincoming : allocation.incomingOrigin = incomingOrigin at hnotOld ⊢
    generalize houtgoing : allocation.outgoingOrigin = outgoingOrigin at hnotOld ⊢
    cases incomingOrigin with
    | oldForward left right successor step =>
        simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward] at hnotOld
    | successorForward incomingLeft incomingRight incomingSuccessor incomingStep =>
        cases outgoingOrigin with
        | oldForward left right successor step =>
            simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward] at hnotOld
        | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
            exact .inl ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward],
              by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward]⟩
        | oldCenter outgoingPosition outgoingStep =>
            exact .inr (.inl
              ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward],
                by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter]⟩)
    | oldCenter incomingPosition incomingStep =>
        cases outgoingOrigin with
        | oldForward left right successor step =>
            simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward] at hnotOld
        | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
            exact .inr (.inr
              ⟨by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter],
                by simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward]⟩)
        | oldCenter outgoingPosition outgoingStep =>
            exact False.elim (InteriorOccurrence.not_both_incident_edges_oldCenter
              occurrence hpath incomingPosition incomingStep
                outgoingPosition outgoingStep hfaceSecond)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
