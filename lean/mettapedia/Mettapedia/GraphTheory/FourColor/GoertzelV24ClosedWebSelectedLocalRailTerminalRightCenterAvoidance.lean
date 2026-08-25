import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailExactTerminalWindow

/-!
# L1: right-centre avoidance for an exact selected terminal window

A source-square bypass introduces one new face: the centre of the successor
Cell--3 placement.  This module identifies the exact local condition under
which either terminal track avoids that centre.  Every old local-rail support
face has a selected side-slot origin; if such a face collapsed onto the next
centre, the two consecutive corridor centres would share two distinct
interior edges.  The successor rails avoid their own centre by irreflexivity.

Thus the already isolated `sharedInteriorEdges.card <= 1` condition implies
right-centre avoidance for both exact terminal supports.  This is a local
preservation lemma, not a proof of that cardinality condition, a rolling rail
assembly, an end cap, a separated crosscut constructor, or Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
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

/-- Every support face of a rail whose edges retain selected forward origins
is one of the placement's selected side faces. -/
theorem exists_selectedSidePosition_of_mem_support
    {incoming outgoing :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    (rail : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
        (selectedPlacementSideFace leftPlacement incoming)
        (selectedPlacementSideFace leftPlacement outgoing))
    (horigin : ∀ edge ∈ rail.edges,
      SelectedPlacementForwardEdgeOrigin leftPlacement edge)
    {face : SelectedFace (web := web)} (hface : face ∈ rail.support) :
    ∃ position :
        {position // position ∈ selectedPlacementSidePositions leftPlacement},
      face = selectedPlacementSideFace leftPlacement position := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mp hface with
    hend | ⟨edge, hedge, hfaceEdge⟩
  · exact ⟨outgoing, hend⟩
  · rcases horigin edge hedge with ⟨first, second, _, receipt⟩
    rw [receipt.edge_eq, Sym2.mem_iff] at hfaceEdge
    rcases hfaceEdge with hfirst | hsecond
    · exact ⟨first, hfirst⟩
    · exact ⟨second, hsecond⟩

/-- The first old local rail avoids the next centre under the exact local
no-double-intersection condition. -/
theorem firstRail_nextCenter_not_mem_of_card_le_one
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        leftInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior leftInterior hnext).center ∉
      left.paths.firstRail.support := by
  intro hmem
  rcases exists_selectedSidePosition_of_mem_support left.paths.firstRail
      left.firstRail_edge_has_forward_origin hmem with ⟨position, hface⟩
  exact (selectedSideFace_ne_nextCenter_of_successorSharedInteriorEdges_card_le_one
    (corridor := corridor) hnext leftPlacement position hcard) hface.symm

/-- The symmetric statement for the second old local rail. -/
theorem secondRail_nextCenter_not_mem_of_card_le_one
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        leftInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior leftInterior hnext).center ∉
      left.paths.secondRail.support := by
  intro hmem
  rcases exists_selectedSidePosition_of_mem_support left.paths.secondRail
      left.secondRail_edge_has_forward_origin hmem with ⟨position, hface⟩
  exact (selectedSideFace_ne_nextCenter_of_successorSharedInteriorEdges_card_le_one
    (corridor := corridor) hnext leftPlacement position hcard) hface.symm

/-- Every face in the exact five-piece adjacent carrier avoids the successor
centre under the same local cardinality condition. -/
theorem ne_nextCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
    {face : SelectedFace (web := web)}
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        leftInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center).1).card ≤ 1)
    (hface : FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face) :
    face ≠ corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      (nextCorridorInterior leftInterior hnext).center := by
  rcases hface with hcenter | hfirst | hsecond | hrightFirst | hrightSecond
  · rw [hcenter]
    exact corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt_ne (by
        intro h
        have hval := congrArg Fin.val h
        simp [nextCorridorInterior] at hval)
  · exact fun hface =>
      firstRail_nextCenter_not_mem_of_card_le_one
        (left := left) hcard (hface ▸ hfirst)
  · exact fun hface =>
      secondRail_nextCenter_not_mem_of_card_le_one
        (left := left) hcard (hface ▸ hsecond)
  · intro hface
    have hfull : face ∈ successor.rightRails.paths.firstRail.support := by
      rw [← successor.firstContinuation_support]
      exact hrightFirst
    exact (successor.rightRails.paths.firstRail_support_adjacent_center face
      hfull).ne (by simpa [hface])
  · intro hface
    have hfull : face ∈ successor.rightRails.paths.secondRail.support := by
      rw [← successor.secondContinuation_support]
      exact hrightSecond
    exact (successor.rightRails.paths.secondRail_support_adjacent_center face
      hfull).ne (by simpa [hface])

/-- The first exact terminal support avoids the right centre. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.rightCenter_not_mem_firstSupport_of_card_le_one
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left)
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        leftInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior leftInterior hnext).center ∉
      window.toCertified.firstSupport := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly | swapped assembly =>
      intro hmem
      exact (ne_nextCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
        hcard (hexact.1 _ hmem)) rfl

/-- The second exact terminal support has the same avoidance property. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.rightCenter_not_mem_secondSupport_of_card_le_one
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left)
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        leftInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior leftInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior leftInterior hnext).center ∉
      window.toCertified.secondSupport := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly | swapped assembly =>
      intro hmem
      exact (ne_nextCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
        hcard (hexact.2 _ hmem)) rfl

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
