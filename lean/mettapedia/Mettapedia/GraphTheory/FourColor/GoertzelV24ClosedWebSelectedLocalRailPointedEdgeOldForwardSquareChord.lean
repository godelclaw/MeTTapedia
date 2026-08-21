import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeFaceAllocation

/-!
# L1: old-forward incidence exposes the square diagonal

For an actual pointed collision on the canonical first--third square, an
old-forward receipt at the second Cell--3 placement does not first ask for a
boundary-edge orientation.  Its collision face is one of that placement's
side faces and is therefore adjacent to the second corridor centre.  Those
are the two opposite vertices of the canonical four-cycle, so the adjacency
is the literal missing diagonal of the square.

This is finite local-classification data supporting L1.  It does not consume
the chord, repair a rail, iterate the rolling transition, attach end caps,
construct separated crosscuts, or close L1.
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
    {left right :
      {position // position ∈ selectedPlacementSidePositions secondPlacement}}
    {edge : Sym2 (SelectedFace web)}

/-- **L1 old-forward square-diagonal classification.**  When the collision
face of the canonical first--third square is one endpoint face of an
old-forward receipt at the second placement, that receipt exposes the missing
second-centre--collision-face chord of the literal four-cycle. -/
theorem SelectedPlacementSideForwardEdgeReceipt.sourceSquare_secondFace_isChord
    (_receipt : SelectedPlacementSideForwardEdgeReceipt
      secondPlacement left right edge)
    {face : SelectedFace web}
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
        (nextCorridorInterior firstInterior hfirstNext).center)
    (hface : face = selectedPlacementSideFace secondPlacement left ∨
      face = selectedPlacementSideFace secondPlacement right) :
    let square := squareDualCycle_of_firstThirdSquare
      (rungs := rungs) hfirst hthird hfaceSecond
    square.cycle.walk.IsChord
      s(corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (nextCorridorInterior firstInterior hfirstNext).center,
        face) := by
  dsimp only
  let square := squareDualCycle_of_firstThirdSquare
    (rungs := rungs) hfirst hthird hfaceSecond
  rw [SimpleGraph.Walk.isChord_sym2Mk]
  have hadj : (SelectedDualGraph web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face := by
    rcases hface with rfl | rfl
    · exact selectedPlacementSideFace_adjacent_center
        (corridor := corridor) secondPlacement left
    · exact selectedPlacementSideFace_adjacent_center
        (corridor := corridor) secondPlacement right
  refine ⟨hadj, ?_, ?_, ?_⟩
  · let skeleton :=
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    have hfirstSecond : skeleton.faceAt firstInterior.center ≠
        skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center :=
      skeleton.faceAt_ne (by
        intro h
        have hval := congrArg Fin.val h
        change firstInterior.center.val = firstInterior.center.val + 1 at hval
        omega)
    have hsecondThird :
        skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center ≠
          skeleton.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center :=
      skeleton.faceAt_ne (by
        intro h
        have hval := congrArg Fin.val h
        change firstInterior.center.val + 1 =
          firstInterior.center.val + 1 + 1 at hval
        omega)
    let firstFace := skeleton.faceAt firstInterior.center
    let secondFace :=
      skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center
    let thirdFace := skeleton.faceAt (nextCorridorInterior
      (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
    have hdiagonalFirst : s(secondFace, face) ≠ s(firstFace, secondFace) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hsecondFirst, _⟩ | ⟨_, hfaceFirst⟩
      · exact hfirstSecond hsecondFirst.symm
      · exact hfirst.ne hfaceFirst.symm
    have hdiagonalSecond : s(secondFace, face) ≠ s(secondFace, thirdFace) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, hfaceThird⟩ | ⟨hsecondThird', _⟩
      · exact hthird.ne hfaceThird.symm
      · exact hsecondThird hsecondThird'
    have hdiagonalThird : s(secondFace, face) ≠ s(thirdFace, face) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hsecondThird', _⟩ | ⟨hsecondFace, _⟩
      · exact hsecondThird hsecondThird'
      · exact hadj.ne hsecondFace
    have hdiagonalFourth : s(secondFace, face) ≠ s(face, firstFace) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hsecondFace, _⟩ | ⟨hsecondFirst, _⟩
      · exact hadj.ne hsecondFace
      · exact hfirstSecond hsecondFirst.symm
    change s(skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center,
        face) ∉
      [s(skeleton.faceAt firstInterior.center,
          skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center),
       s(skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center,
          skeleton.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center),
       s(skeleton.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center,
          face),
       s(face, skeleton.faceAt firstInterior.center)]
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    · exact hdiagonalFirst (by simpa [firstFace, secondFace] using hmem)
    · exact hdiagonalSecond (by simpa [secondFace, thirdFace] using hmem)
    · exact hdiagonalThird (by simpa [secondFace, thirdFace] using hmem)
    · exact hdiagonalFourth (by simpa [firstFace, secondFace] using hmem)
  · have hmem := square.cycle.walk.getVert_mem_support 1
    simpa [square] using hmem
  · have hmem := square.cycle.walk.getVert_mem_support 3
    simpa [square] using hmem

/-- Whether a proof-relevant adjacent-terminal origin is a forward step from
the older of the two displayed placements. -/
def SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward
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
  | .oldForward _ _ _ _ => True
  | .successorForward _ _ _ _ | .oldCenter _ _ => False

/-- An actual incoming pointed edge at the square collision is either not an
old-placement forward edge, or it exhibits the literal second--collision
diagonal of the canonical square. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.incoming_isChord_or_notOldForward
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
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
      ¬ allocation.incomingOrigin.IsOldForward := by
  dsimp only
  generalize horigin : allocation.incomingOrigin = origin
  cases origin with
  | oldForward left right successor step =>
      left
      have hfaces := allocation.incomingFaces
      rw [horigin] at hfaces
      have hface : face = selectedPlacementSideFace secondPlacement left ∨
          face = selectedPlacementSideFace secondPlacement right := by
        rcases hfaces with hfaces | hfaces
        · exact .inr hfaces.2
        · exact .inl hfaces.2
      exact Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.sourceSquare_secondFace_isChord
        step hfirst hthird hfaceSecond hface
  | successorForward left right successor step =>
      right
      simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward]
  | oldCenter position step =>
      right
      simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward]

/-- The outgoing pointed edge has the same fail-closed classification: an
old-placement forward origin supplies the square diagonal; otherwise its
proof-relevant origin remains explicitly outside that case. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.outgoing_isChord_or_notOldForward
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
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
      ¬ allocation.outgoingOrigin.IsOldForward := by
  dsimp only
  generalize horigin : allocation.outgoingOrigin = origin
  cases origin with
  | oldForward left right successor step =>
      left
      have hfaces := allocation.outgoingFaces
      rw [horigin] at hfaces
      have hface : face = selectedPlacementSideFace secondPlacement left ∨
          face = selectedPlacementSideFace secondPlacement right := by
        rcases hfaces with hfaces | hfaces
        · exact .inl hfaces.1
        · exact .inr hfaces.1
      exact Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly.SelectedPlacementSideForwardEdgeReceipt.sourceSquare_secondFace_isChord
        step hfirst hthird hfaceSecond hface
  | successorForward left right successor step =>
      right
      simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward]
  | oldCenter position step =>
      right
      simp [SelectedAdjacentTerminalEdgeCrossingOrigin.IsOldForward]

/-- Combined pointed classification.  Unless the canonical source square has
the literal second--collision diagonal, neither incident pointed edge can
come from an old-placement forward step. -/
theorem InteriorOccurrence.SelectedAdjacentPointedFaceAllocation.sourceSquare_isChord_or_incidentOrigins_notOldForward
    {start finish face : SelectedFace web}
    {walk : (SelectedDualGraph web).Walk start finish}
    {occurrence : InteriorOccurrence (current := face) walk}
    (allocation : InteriorOccurrence.SelectedAdjacentPointedFaceAllocation
      (leftPlacement := secondPlacement) (rightPlacement := thirdPlacement)
      occurrence)
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
      (¬ allocation.incomingOrigin.IsOldForward ∧
        ¬ allocation.outgoingOrigin.IsOldForward) := by
  dsimp only
  rcases allocation.incoming_isChord_or_notOldForward
      hfirst hthird hfaceSecond with hchord | hincoming
  · exact .inl hchord
  · rcases allocation.outgoing_isChord_or_notOldForward
        hfirst hthird hfaceSecond with hchord | houtgoing
    · exact .inl hchord
    · exact .inr ⟨hincoming, houtgoing⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
