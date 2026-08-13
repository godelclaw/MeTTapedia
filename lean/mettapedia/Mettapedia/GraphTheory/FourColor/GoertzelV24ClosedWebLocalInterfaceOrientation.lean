import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalInterfaceMatching

/-!
# Orientation at consecutive source-local Cell-3 interfaces

The local Cell-3 construction already knows that the outgoing rung of one
corridor face is the incoming rung of the next.  This file records the
oriented-dart form of that fact directly on the closed-web carrier.  It is a
local interface fact only: it neither constructs a long annular transversal
nor treats overlapping local layer windows as a serial open-tangle composite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- Advancing one internal corridor face makes its incoming corridor step
definitionally the preceding face's outgoing step.  This is index arithmetic,
not a global annular construction. -/
theorem nextLocalCorridorInterior_incoming_eq_outgoing
    {corridorLength : Nat} (interior : CorridorInterior corridorLength)
    (hnext : interior.center.val + 2 < corridorLength) :
    (nextCorridorInterior interior hnext).incoming = interior.outgoing := by
  have hleft : (nextCorridorInterior interior hnext).incoming.left =
      interior.outgoing.left := by
    simp [nextCorridorInterior, CorridorInterior.incoming,
      CorridorInterior.outgoing]
  cases hright : (nextCorridorInterior interior hnext).incoming with
  | mk rightLeft rightProof =>
      cases hleftStep : interior.outgoing with
      | mk leftLeft leftProof =>
          simp only [hright, hleftStep, CorridorStep.mk.injEq] at hleft ⊢
          exact hleft

/-- **L9 (local interface orientation).** The literal incoming dart of a
consecutive Cell-3 face is the `alpha`-opposite of the preceding outgoing
dart.  The proof uses the actual local interior-face certificate, rather than
assuming globally two-sided annular faces. -/
theorem nextLocalPlacement_incomingDart_eq_alpha_outgoingDart
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    faceCycleDart web.annular.RS rightPlacement.root rightPlacement.incomingPosition =
      web.annular.RS.alpha
        (faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition) := by
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftDart :=
    faceCycleDart web.annular.RS leftPlacement.root leftPlacement.outgoingPosition
  let rightDart :=
    faceCycleDart web.annular.RS rightPlacement.root rightPlacement.incomingPosition
  have hsteps : rightInterior.incoming = leftInterior.outgoing := by
    simpa [rightInterior] using
      nextLocalCorridorInterior_incoming_eq_outgoing leftInterior hnext
  have hedge : web.annular.RS.edgeOf rightDart = web.annular.RS.edgeOf leftDart := by
    calc
      web.annular.RS.edgeOf rightDart =
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.rungEdge
            hunique rightInterior.incoming := rightPlacement.incoming_edge
      _ = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.rungEdge
            hunique leftInterior.outgoing := by rw [hsteps]
      _ = web.annular.RS.edgeOf leftDart := leftPlacement.outgoing_edge.symm
  have hleftFace : dartOrbitFace web.annular.RS leftDart =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center).1 := by
    calc
      dartOrbitFace web.annular.RS leftDart =
          dartOrbitFace web.annular.RS leftPlacement.root :=
        dartOrbitFace_faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        leftInterior.center).1 := leftPlacement.root_face
  have hleftInternal : dartOrbitFace web.annular.RS leftDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [hleftFace]
    exact corridor.face_internal leftInterior.center
  have hrightFace : dartOrbitFace web.annular.RS rightDart =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := by
    calc
      dartOrbitFace web.annular.RS rightDart =
          dartOrbitFace web.annular.RS rightPlacement.root :=
        dartOrbitFace_faceCycleDart web.annular.RS rightPlacement.root
          rightPlacement.incomingPosition
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := rightPlacement.root_face
  have halphaFace : dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) =
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := by
    simpa [rightInterior, nextCorridorInterior] using
      localOutgoingAlphaFace_eq_nextCenter (corridor := corridor) hnext leftPlacement
  rcases web.annular.RS.edge_fiber_two_cases
      (e := web.annular.RS.edgeOf leftDart) (d := leftDart) (y := rightDart)
      rfl hedge with hsame | hopposite
  · exfalso
    apply InteriorFace.dartOrbitFace_ne_alpha web leftDart hleftInternal
    calc
      dartOrbitFace web.annular.RS leftDart =
          dartOrbitFace web.annular.RS rightDart :=
        congrArg (dartOrbitFace web.annular.RS) hsame.symm
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        rightInterior.center).1 := hrightFace
      _ = dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart) :=
        halphaFace.symm
  · exact hopposite

/-- **L9 (local rail identification).** The first third-edge rail at an
outgoing Cell-3 corner is a literal side edge of the next source face.  The
matched face alone would be too weak for a later primal-boundary assembly, so
this statement retains the equality of the actual ambient edges.  It is still
only a one-step local interface fact. -/
theorem exists_nextLocalPlacementSideEdge_eq_beforeOutgoingCornerEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (leftPosition : {position // position ∈ placementSidePositions leftPlacement})
    (hsuccessor : leftPlacement.outgoingPosition.val ≡
      leftPosition.1.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    ∃ rightPosition : {position // position ∈ placementSidePositions rightPlacement},
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightPlacement.root rightPosition.1) =
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS leftPlacement.root leftPosition.1))) ∧
      localPlacementSideFace leftPlacement leftPosition =
        localPlacementSideFace rightPlacement rightPosition := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftFace := localPlacementSideFace leftPlacement leftPosition
  let rightCenter := skeleton.faceAt rightInterior.center
  have hadjRaw := localPlacementSideFace_adjacent_next_of_before_outgoing
    (corridor := corridor) hnext leftPlacement leftPosition hsuccessor
  have hadj : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        rightCenter leftFace := by
    simpa [rightCenter, rightInterior, leftFace, skeleton,
      nextCorridorInterior] using hadjRaw.symm
  have hleftExternal : ∀ index : Fin blockLength,
      leftFace ≠ skeleton.faceAt index := by
    intro index
    simpa [leftFace, skeleton] using
      localPlacementSideFace_ne_faceAt (corridor := corridor)
        leftPlacement leftPosition index
  rcases exists_localPlacementSideFace_eq_of_adjacent_external
      (corridor := corridor) rightPlacement leftFace hadj hleftExternal with
    ⟨rightPosition, hrightFace⟩
  let rightDart :=
    faceCycleDart web.annular.RS rightPlacement.root rightPosition.1
  have hrightBoundary : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS rightCenter.1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS rightDart
    rw [dartOrbitFace_faceCycleDart, rightPlacement.root_face] at hraw
    simpa [rightDart, rightCenter, rightInterior, skeleton] using hraw
  have hrightAcross : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS leftFace.1 := by
    rw [← hrightFace]
    change web.annular.RS.edgeOf rightDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha rightDart))
    rw [← web.annular.RS.edge_alpha rightDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha rightDart)
  have hrightInterior : web.annular.RS.edgeOf rightDart ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
    apply InteriorFace.edge_mem_interiorEdgeSupport web rightDart
    exact localPlacementSideDart_internal (corridor := corridor)
      rightPlacement rightPosition
  have hrightShared : web.annular.RS.edgeOf rightDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        leftFace.1 rightCenter.1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨hrightInterior, hrightAcross, hrightBoundary⟩
  have hcornerShared : web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi
        (faceCycleDart web.annular.RS leftPlacement.root leftPosition.1))) ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        leftFace.1 rightCenter.1 := by
    simpa [leftFace, rightCenter, rightInterior, skeleton,
      nextCorridorInterior] using
      localPlacementThirdEdge_mem_sharedInteriorEdges_of_before_outgoing
        (corridor := corridor) hnext leftPlacement leftPosition hsuccessor
  have hfaceNe : leftFace.1 ≠ rightCenter.1 := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces.symm)
  have hedgeEq : web.annular.RS.edgeOf rightDart =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi
          (faceCycleDart web.annular.RS leftPlacement.root leftPosition.1))) :=
    (Finset.card_le_one_iff.1
      (hunique leftFace.1 leftFace.2 rightCenter.1 rightCenter.2 hfaceNe))
      hrightShared hcornerShared
  exact ⟨rightPosition, hedgeEq, hrightFace.symm⟩

/-- **L9 (local rail identification).** The second third-edge rail at an
outgoing Cell-3 corner is also a literal side edge of the next source face.
Together with `exists_nextLocalPlacementSideEdge_eq_beforeOutgoingCornerEdge`,
this identifies both rail tracks on the actual closed-web carrier; it still
makes no global simplicity or annular-transversal claim. -/
theorem exists_nextLocalPlacementSideEdge_eq_afterOutgoingCornerEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    (hnext : leftInterior.center.val + 2 < blockLength)
    (leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior)
    (leftPosition : {position // position ∈ placementSidePositions leftPlacement})
    (hsuccessor : leftPosition.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6])
    (rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)) :
    ∃ rightPosition : {position // position ∈ placementSidePositions rightPlacement},
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightPlacement.root rightPosition.1) =
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS leftPlacement.root
              leftPlacement.outgoingPosition))) ∧
      localPlacementSideFace leftPlacement leftPosition =
        localPlacementSideFace rightPlacement rightPosition := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  let leftFace := localPlacementSideFace leftPlacement leftPosition
  let rightCenter := skeleton.faceAt rightInterior.center
  have hadjRaw := localPlacementSideFace_adjacent_next_of_after_outgoing
    (corridor := corridor) hnext leftPlacement leftPosition hsuccessor
  have hadj : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        rightCenter leftFace := by
    simpa [rightCenter, rightInterior, leftFace, skeleton,
      nextCorridorInterior] using hadjRaw.symm
  have hleftExternal : ∀ index : Fin blockLength,
      leftFace ≠ skeleton.faceAt index := by
    intro index
    simpa [leftFace, skeleton] using
      localPlacementSideFace_ne_faceAt (corridor := corridor)
        leftPlacement leftPosition index
  rcases exists_localPlacementSideFace_eq_of_adjacent_external
      (corridor := corridor) rightPlacement leftFace hadj hleftExternal with
    ⟨rightPosition, hrightFace⟩
  let rightDart :=
    faceCycleDart web.annular.RS rightPlacement.root rightPosition.1
  have hrightBoundary : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS rightCenter.1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS rightDart
    rw [dartOrbitFace_faceCycleDart, rightPlacement.root_face] at hraw
    simpa [rightDart, rightCenter, rightInterior, skeleton] using hraw
  have hrightAcross : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS leftFace.1 := by
    rw [← hrightFace]
    change web.annular.RS.edgeOf rightDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha rightDart))
    rw [← web.annular.RS.edge_alpha rightDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha rightDart)
  have hrightInterior : web.annular.RS.edgeOf rightDart ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
    apply InteriorFace.edge_mem_interiorEdgeSupport web rightDart
    exact localPlacementSideDart_internal (corridor := corridor)
      rightPlacement rightPosition
  have hrightShared : web.annular.RS.edgeOf rightDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        rightCenter.1 leftFace.1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨hrightInterior, hrightBoundary, hrightAcross⟩
  have hcornerShared : web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi
        (faceCycleDart web.annular.RS leftPlacement.root
          leftPlacement.outgoingPosition))) ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        rightCenter.1 leftFace.1 := by
    simpa [leftFace, rightCenter, rightInterior, skeleton,
      nextCorridorInterior] using
      localPlacementThirdEdge_mem_sharedInteriorEdges_of_after_outgoing
        (corridor := corridor) hnext leftPlacement leftPosition hsuccessor
  have hfaceNe : rightCenter.1 ≠ leftFace.1 := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces)
  have hedgeEq : web.annular.RS.edgeOf rightDart =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi
          (faceCycleDart web.annular.RS leftPlacement.root
            leftPlacement.outgoingPosition))) :=
    (Finset.card_le_one_iff.1
      (hunique rightCenter.1 rightCenter.2 leftFace.1 leftFace.2 hfaceNe))
      hrightShared hcornerShared
  exact ⟨rightPosition, hedgeEq, hrightFace.symm⟩

/-- **L9 (canonical local rail cell).** The canonical Cell-3 placement and
its successor carry two distinct matched rail slots, and both matches retain
the literal ambient edge as well as the intervening side face.  This is the
one-step cell needed by a later lengthwise assembly; it does not assert that
iterating the cells gives simple paths or reaches the annular end caps. -/
theorem exists_canonicalNextLocalPlacementRailEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    let witness := localLayerPairWitnessOfCorridor
      corridor hunique leftInterior hnext
    let rightPlacement := localInternalHexRungPlacement corridor hunique
      (nextCorridorInterior leftInterior hnext)
    ∃ rightBefore rightAfter :
        {position // position ∈ placementSidePositions rightPlacement},
      rightBefore ≠ rightAfter ∧
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightPlacement.root rightBefore.1) =
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.before.1))) ∧
      localPlacementSideFace witness.placement witness.before =
        localPlacementSideFace rightPlacement rightBefore ∧
      web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS rightPlacement.root rightAfter.1) =
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.placement.outgoingPosition))) ∧
      localPlacementSideFace witness.placement witness.after =
        localPlacementSideFace rightPlacement rightAfter := by
  let witness := localLayerPairWitnessOfCorridor
    corridor hunique leftInterior hnext
  let rightPlacement := localInternalHexRungPlacement corridor hunique
    (nextCorridorInterior leftInterior hnext)
  rcases exists_nextLocalPlacementSideEdge_eq_beforeOutgoingCornerEdge
      (corridor := corridor) hnext witness.placement witness.before
      witness.outgoing_after_before rightPlacement with
    ⟨rightBefore, hbeforeEdge, hbeforeFace⟩
  rcases exists_nextLocalPlacementSideEdge_eq_afterOutgoingCornerEdge
      (corridor := corridor) hnext witness.placement witness.after
      witness.after_after_outgoing rightPlacement with
    ⟨rightAfter, hafterEdge, hafterFace⟩
  have hrightNe : rightBefore ≠ rightAfter := by
    intro heq
    apply witness.before_ne_after
    apply localPlacementSideFace_injective (corridor := corridor)
      witness.placement
    rw [hbeforeFace, hafterFace, heq]
  exact ⟨rightBefore, rightAfter, hrightNe, hbeforeEdge, hbeforeFace,
    hafterEdge, hafterFace⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
