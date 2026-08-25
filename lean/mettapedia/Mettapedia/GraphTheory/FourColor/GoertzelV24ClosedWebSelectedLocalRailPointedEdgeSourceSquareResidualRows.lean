import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeSourceSquareChordTriangles
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeOppositeEndpointBypass

/-!
# L1: bypass the three residual source-square origin rows

After the old-forward rows enter the selected square-chord reduction, exactly
three pointed origin rows remain.  They are all literal two-step bypasses
through the centre of the successor Cell--3 placement:

* successor / successor: side -- successor centre -- side;
* successor / old centre: side -- successor centre -- old centre;
* old centre / successor: old centre -- successor centre -- side.

This is the finite local classification required by the source corridor
construction.  It does not discharge the cyclic chord-triangle alternative,
splice the bypass into the full rail, iterate the repair, attach end caps,
construct separated crosscuts, or close L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
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

/-- The two corridor centres used in all three residual bypasses are adjacent
by the literal selected corridor interface. -/
private theorem secondCenter_adj_thirdCenter :
    (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) := by
  exact (corridor.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton).consecutive_adjacent
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center rfl

/-- A residual source-square bypass together with the exact local support
receipt which the paired-rail construction needs.  The two endpoints already
belong to the old rail; the displayed third Cell--3 centre is the only new
face whose separation from the companion rail remains to be proved. -/
structure InteriorOccurrence.SourceSquareTwoHopBypass
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := face) walk) where
  toTwoHopBypass : InteriorOccurrence.TwoHopBypass occurrence
  support_subset : ∀ vertex ∈ toTwoHopBypass.walk.support,
    vertex = occurrence.predecessor ∨
      vertex =
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
      vertex = occurrence.successor

/-- **L1 finite residual-row bypass.**  Each of the three non-old-forward
origin rows constructs a two-step pointed bypass through the successor
Cell--3 centre, retaining the fact that this centre is its only new support
face. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquareTwoHopBypass_of_three_origin_rows
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (hrows :
      (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsSuccessorForward) ∨
        (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsOldCenter) ∨
        (allocation.incomingOrigin.IsOldCenter ∧
          allocation.outgoingOrigin.IsSuccessorForward)) :
    Nonempty (InteriorOccurrence.SourceSquareTwoHopBypass
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence) := by
  let secondCenter :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior firstInterior hfirstNext).center
  let thirdCenter :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
  have hcenters : (SelectedDualGraph web).Adj secondCenter thirdCenter :=
    secondCenter_adj_thirdCenter
  have hfaceThird : face ≠ thirdCenter := hthird.ne.symm
  generalize hincoming : allocation.incomingOrigin = incomingOrigin at hrows
  cases incomingOrigin with
  | oldForward incomingLeft incomingRight incomingSuccessor incomingStep =>
      simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward,
        SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter] at hrows
  | successorForward incomingLeft incomingRight incomingSuccessor incomingStep =>
      have hincomingFaces := allocation.incomingFaces
      rw [hincoming] at hincomingFaces
      have hpredecessorThird : (SelectedDualGraph web).Adj
          occurrence.predecessor thirdCenter := by
        rcases hincomingFaces with hincomingFaces | hincomingFaces
        · rw [hincomingFaces.1]
          exact (selectedPlacementSideFace_adjacent_center
            (corridor := corridor) thirdPlacement incomingLeft).symm
        · rw [hincomingFaces.1]
          exact (selectedPlacementSideFace_adjacent_center
            (corridor := corridor) thirdPlacement incomingRight).symm
      generalize houtgoing : allocation.outgoingOrigin = outgoingOrigin at hrows
      cases outgoingOrigin with
      | oldForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward,
            SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter] at hrows
      | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          have houtgoingFaces := allocation.outgoingFaces
          rw [houtgoing] at houtgoingFaces
          have hthirdSuccessor : (SelectedDualGraph web).Adj
              thirdCenter occurrence.successor := by
            rcases houtgoingFaces with houtgoingFaces | houtgoingFaces
            · rw [houtgoingFaces.2]
              exact selectedPlacementSideFace_adjacent_center
                (corridor := corridor) thirdPlacement outgoingRight
            · rw [houtgoingFaces.2]
              exact selectedPlacementSideFace_adjacent_center
                (corridor := corridor) thirdPlacement outgoingLeft
          exact ⟨{
            toTwoHopBypass := {
              walk := .cons hpredecessorThird (.cons hthirdSuccessor .nil)
              length_le_two := by simp
              current_not_mem_support := by
                simp [occurrence.predecessor_ne_current.symm,
                  occurrence.current_ne_successor, hfaceThird]
            }
            support_subset := by simp [thirdCenter]
          }⟩
      | oldCenter outgoingPosition outgoingStep =>
          have hsuccessorSecond : occurrence.successor = secondCenter := by
            exact InteriorOccurrence.successor_eq_leftCenter_of_outgoing_oldCenter
              occurrence outgoingPosition outgoingStep hfaceSecond
          have hthirdSuccessor : (SelectedDualGraph web).Adj
              thirdCenter occurrence.successor := by
            rw [hsuccessorSecond]
            exact hcenters.symm
          exact ⟨{
            toTwoHopBypass := {
              walk := .cons hpredecessorThird (.cons hthirdSuccessor .nil)
              length_le_two := by simp
              current_not_mem_support := by
                simp [occurrence.predecessor_ne_current.symm,
                  occurrence.current_ne_successor, hfaceThird]
            }
            support_subset := by simp [thirdCenter]
          }⟩
  | oldCenter incomingPosition incomingStep =>
      have hpredecessorSecond : occurrence.predecessor = secondCenter := by
        exact InteriorOccurrence.predecessor_eq_leftCenter_of_incoming_oldCenter
          occurrence incomingPosition incomingStep hfaceSecond
      have hpredecessorThird : (SelectedDualGraph web).Adj
          occurrence.predecessor thirdCenter := by
        rw [hpredecessorSecond]
        exact hcenters
      generalize houtgoing : allocation.outgoingOrigin = outgoingOrigin at hrows
      cases outgoingOrigin with
      | oldForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward,
            SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter] at hrows
      | successorForward outgoingLeft outgoingRight outgoingSuccessor outgoingStep =>
          have houtgoingFaces := allocation.outgoingFaces
          rw [houtgoing] at houtgoingFaces
          have hthirdSuccessor : (SelectedDualGraph web).Adj
              thirdCenter occurrence.successor := by
            rcases houtgoingFaces with houtgoingFaces | houtgoingFaces
            · rw [houtgoingFaces.2]
              exact selectedPlacementSideFace_adjacent_center
                (corridor := corridor) thirdPlacement outgoingRight
            · rw [houtgoingFaces.2]
              exact selectedPlacementSideFace_adjacent_center
                (corridor := corridor) thirdPlacement outgoingLeft
          exact ⟨{
            toTwoHopBypass := {
              walk := .cons hpredecessorThird (.cons hthirdSuccessor .nil)
              length_le_two := by simp
              current_not_mem_support := by
                simp [occurrence.predecessor_ne_current.symm,
                  occurrence.current_ne_successor, hfaceThird]
            }
            support_subset := by simp [thirdCenter]
          }⟩
      | oldCenter outgoingPosition outgoingStep =>
          simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsSuccessorForward,
            SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldCenter] at hrows

/-- The support-sensitive residual constructor implies the earlier plain
two-hop existence interface. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_twoHopBypass_of_three_origin_rows
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (hrows :
      (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsSuccessorForward) ∨
        (allocation.incomingOrigin.IsSuccessorForward ∧
          allocation.outgoingOrigin.IsOldCenter) ∨
        (allocation.incomingOrigin.IsOldCenter ∧
          allocation.outgoingOrigin.IsSuccessorForward)) :
    Nonempty (InteriorOccurrence.TwoHopBypass occurrence) := by
  rcases allocation.exists_sourceSquareTwoHopBypass_of_three_origin_rows
      hthird hfaceSecond hrows with ⟨bypass⟩
  exact ⟨bypass.toTwoHopBypass⟩

/-- **L1 complete source-square local alternative.**  The actual pointed
allocation at a non-flank collision produces either a selected chord triangle
with a cyclic inner side or an explicit two-step bypass around the collision.

Thus the three residual origin rows are fully consumed.  The cyclic separator,
whole-rail splice, rolling iteration, end caps, separated crosscuts, and L1
remain open. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.exists_sourceSquare_chordTriangleCycle_or_sourceSquareTwoHopBypass
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
    (hsecond : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hthird : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center)
    (successor : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement)
    (hneBefore : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftBefore)
    (hneAfter : face ≠
      selectedPlacementSideFace secondPlacement successor.frame.leftAfter) :
    (let square := MiddleReplacementShortDualCycle.squareDualCycleWithSecondRung
      (rungs := rungs) hfirst hthird hfaceSecond
    ∃ selected : square.SourceChordSelectedTriangles
        (secondPlacement := secondPlacement),
      (∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.firstShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
        ∃ component :
          (G.deleteEdges (edgeFinsetValueSet
            selected.secondShortCycle.selectedCycle.crossingEdges)).ConnectedComponent,
        web.annular.RS.outer.fst ∉ component.supp ∧
          HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) ∨
      Nonempty (InteriorOccurrence.SourceSquareTwoHopBypass
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext) occurrence) := by
  dsimp only
  rcases allocation.exists_sourceSquare_chordTriangleCycle_or_three_origin_rows
      hpath hfirst hsecond hthird hfaceSecond successor hneBefore hneAfter with
    hcycle | hrows
  · exact .inl hcycle
  · exact .inr
      (allocation.exists_sourceSquareTwoHopBypass_of_three_origin_rows
        hthird hfaceSecond hrows)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
