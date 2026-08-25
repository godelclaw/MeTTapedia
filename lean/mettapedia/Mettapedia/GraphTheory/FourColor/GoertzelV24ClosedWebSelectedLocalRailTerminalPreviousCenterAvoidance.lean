import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTerminalRightCenterAvoidance

/-!
# L1: previous-centre avoidance for a shifted exact terminal window

The last exact window in a four-cell track begins two corridor steps after
the first window.  Its companion-separation proof therefore needs the mirror
of right-centre avoidance: neither track may return to the centre immediately
before that last window.

This file proves the mirror under the same exact local condition.  If a side
face of the new left placement were the previous centre, its incoming rung
and the literal side edge would be two distinct shared interior edges.
Successor-rail faces are adjacent to the centre two steps away and are
excluded by corridor separation.

The theorem does not assert the local cardinality premise, eliminate its
double-edge alternative, assemble a rolling rail, attach end caps, construct
separated crosscuts, or close Fable flag L1.
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
open GoertzelV24InducedHexCorridorTypes
open SimpleGraphDartRotation

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
    {previousInterior : CorridorInterior blockLength}
    {hnext : previousInterior.center.val + 2 < blockLength}
    {hnextNext :
      (nextCorridorInterior previousInterior hnext).center.val + 2 < blockLength}
    {previousPlacement : SelectedInternalHexRungPlacement corridor rungs
      previousInterior}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior previousInterior hnext)}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior previousInterior hnext) hnextNext)}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnextNext
      leftPlacement rightPlacement}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A selected side face of the next placement cannot be the preceding
corridor centre when those two centres share at most one interior edge. -/
theorem selectedSideFace_ne_previousCenter_of_sharedInteriorEdges_card_le_one
    (previousPlacement : SelectedInternalHexRungPlacement corridor rungs
      previousInterior)
    (position :
      {position // position ∈ selectedPlacementSidePositions leftPlacement})
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        previousInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior previousInterior hnext).center).1).card ≤ 1) :
    selectedPlacementSideFace leftPlacement position ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        previousInterior.center := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let incomingDart := faceCycleDart web.annular.RS leftPlacement.root
    leftPlacement.incomingPosition
  let sideDart := faceCycleDart web.annular.RS leftPlacement.root position.1
  intro hface
  have hincomingInternal : dartOrbitFace web.annular.RS incomingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [dartOrbitFace_faceCycleDart, leftPlacement.root_face]
    exact corridor.face_internal
      (nextCorridorInterior previousInterior hnext).center
  have hsideInternal : dartOrbitFace web.annular.RS sideDart ∈
      web.annular.cellulation.interiorFaces :=
    selectedPlacementSideDart_internal (corridor := corridor)
      leftPlacement position
  have hincomingPrevious : web.annular.RS.edgeOf incomingDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt previousInterior.center).1 := by
    have hincomingEdge : web.annular.RS.edgeOf incomingDart =
        rungs.edge previousInterior.outgoing := by
      calc
        web.annular.RS.edgeOf incomingDart =
            web.annular.RS.edgeOf (web.annular.RS.alpha
              (faceCycleDart web.annular.RS previousPlacement.root
                previousPlacement.outgoingPosition)) := by
          exact congrArg web.annular.RS.edgeOf
            (selectedNextIncomingDart_eq_alpha_outgoingDart
              (corridor := corridor) hnext previousPlacement leftPlacement)
        _ = web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS previousPlacement.root
              previousPlacement.outgoingPosition) :=
          web.annular.RS.edge_alpha _
        _ = rungs.edge previousInterior.outgoing :=
          previousPlacement.outgoing_edge
    rw [hincomingEdge]
    exact rungs.mem_left previousInterior.outgoing
  have hincomingLeft : web.annular.RS.edgeOf incomingDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt
          (nextCorridorInterior previousInterior hnext).center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS incomingDart
    rw [dartOrbitFace_faceCycleDart, leftPlacement.root_face] at hraw
    exact hraw
  have hsideLeft : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt
          (nextCorridorInterior previousInterior hnext).center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, leftPlacement.root_face] at hraw
    exact hraw
  have hsidePrevious : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt previousInterior.center).1 := by
    have hraw : web.annular.RS.edgeOf sideDart ∈
        orbitFaceBoundary web.annular.RS
          (selectedPlacementSideFace leftPlacement position).1 := by
      change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
      rw [← web.annular.RS.edge_alpha sideDart]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
        (web.annular.RS.alpha sideDart)
    rw [hface] at hraw
    exact hraw
  have hincomingShared : web.annular.RS.edgeOf incomingDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt previousInterior.center).1
        (skeleton.faceAt
          (nextCorridorInterior previousInterior hnext).center).1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
        ⟨Instance.InteriorFace.edge_mem_interiorEdgeSupport web incomingDart
            hincomingInternal,
          hincomingPrevious, hincomingLeft⟩
  have hsideShared : web.annular.RS.edgeOf sideDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt previousInterior.center).1
        (skeleton.faceAt
          (nextCorridorInterior previousInterior hnext).center).1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
        ⟨Instance.InteriorFace.edge_mem_interiorEdgeSupport web sideDart
            hsideInternal,
          hsidePrevious, hsideLeft⟩
  have hedges : web.annular.RS.edgeOf incomingDart =
      web.annular.RS.edgeOf sideDart :=
    Finset.card_le_one.mp hcard _ hincomingShared _ hsideShared
  have hpositions : leftPlacement.incomingPosition = position.1 := by
    apply Instance.InteriorFace.faceCycleEdge_injective web leftPlacement.root
      (by
        rw [leftPlacement.root_face]
        exact corridor.face_internal
          (nextCorridorInterior previousInterior hnext).center)
    exact hedges
  exact ((mem_selectedPlacementSidePositions_iff leftPlacement position.1).1
    position.2).1 hpositions.symm

/-- Every face in the shifted adjacent carrier avoids the preceding centre
under the same local cardinality condition. -/
theorem ne_previousCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
    {face : SelectedFace (web := web)}
    (previousPlacement : SelectedInternalHexRungPlacement corridor rungs
      previousInterior)
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        previousInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior previousInterior hnext).center).1).card ≤ 1)
    (hface : FaceInAdjacentSelectedRailPieces (successor := successor)
      (left := left) face) :
    face ≠ corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
      previousInterior.center := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  rcases hface with hcenter | hfirst | hsecond | hrightFirst | hrightSecond
  · rw [hcenter]
    exact skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      simp [nextCorridorInterior] at hval)
  · intro heq
    rcases exists_selectedSidePosition_of_mem_support left.paths.firstRail
        left.firstRail_edge_has_forward_origin hfirst with ⟨position, hposition⟩
    exact selectedSideFace_ne_previousCenter_of_sharedInteriorEdges_card_le_one
      previousPlacement position hcard
      (hposition.symm.trans heq)
  · intro heq
    rcases exists_selectedSidePosition_of_mem_support left.paths.secondRail
        left.secondRail_edge_has_forward_origin hsecond with ⟨position, hposition⟩
    exact selectedSideFace_ne_previousCenter_of_sharedInteriorEdges_card_le_one
      previousPlacement position hcard
      (hposition.symm.trans heq)
  · intro heq
    have hfull : face ∈ successor.rightRails.paths.firstRail.support := by
      rw [← successor.firstContinuation_support]
      exact hrightFirst
    have hadj := successor.rightRails.paths.firstRail_support_adjacent_center face hfull
    subst face
    exact (skeleton.separated_not_adjacent previousInterior.center
      (nextCorridorInterior
        (nextCorridorInterior previousInterior hnext) hnextNext).center
      (by simp [nextCorridorInterior])) hadj.symm
  · intro heq
    have hfull : face ∈ successor.rightRails.paths.secondRail.support := by
      rw [← successor.secondContinuation_support]
      exact hrightSecond
    have hadj := successor.rightRails.paths.secondRail_support_adjacent_center face hfull
    subst face
    exact (skeleton.separated_not_adjacent previousInterior.center
      (nextCorridorInterior
        (nextCorridorInterior previousInterior hnext) hnextNext).center
      (by simp [nextCorridorInterior])) hadj.symm

/-- The first exact shifted-terminal support avoids the preceding centre. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.previousCenter_not_mem_firstSupport_of_card_le_one
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left)
    (previousPlacement : SelectedInternalHexRungPlacement corridor rungs
      previousInterior)
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        previousInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior previousInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        previousInterior.center ∉ window.toCertified.firstSupport := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly | swapped assembly =>
      intro hmem
      exact (ne_previousCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
        previousPlacement hcard (hexact.1 _ hmem)) rfl

/-- The second exact shifted-terminal support has the same avoidance. -/
theorem ExactCertifiedSelectedLocalRailTerminalWindow.previousCenter_not_mem_secondSupport_of_card_le_one
    (window : ExactCertifiedSelectedLocalRailTerminalWindow successor left)
    (previousPlacement : SelectedInternalHexRungPlacement corridor rungs
      previousInterior)
    (hcard : (sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        previousInterior.center).1
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior previousInterior hnext).center).1).card ≤ 1) :
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        previousInterior.center ∉ window.toCertified.secondSupport := by
  rcases window with ⟨outcome, hexact⟩
  cases outcome with
  | straight assembly | swapped assembly =>
      intro hmem
      exact (ne_previousCenter_of_mem_adjacentSelectedRailPieces_of_card_le_one
        previousPlacement hcard (hexact.2 _ hmem)) rfl

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
