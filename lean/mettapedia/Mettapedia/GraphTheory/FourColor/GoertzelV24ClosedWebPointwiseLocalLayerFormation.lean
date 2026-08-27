import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFormation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerPointwiseCrossings

/-!
# Forming a literal Cell-3 layer from pointwise source geometry

This is the consumer-facing bridge from the corrected finite source witness to
the colouring-free `Formation.LocalLayerPair`.  A side face is the face of the
opposite dart at one of the four non-rung slots.  The two slots flanking the
outgoing rung meet the next corridor hexagon at the two locally cubic corners.

Every uniqueness use is restricted to the displayed annular-interior face
pair.  In particular, neither hole face and no global opened-annulus
intersection hypothesis occurs in the interface.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPointwiseRungs
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Formation

namespace LocalLayerFormation

/-- The face across one of the four literal non-rung positions. -/
noncomputable def pointwiseLocalPlacementSideFace
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    AmbientFace (Finset.univ : Finset (OrbitFace formation.annular.RS)) :=
  ⟨dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha
        (faceCycleDart formation.annular.RS placement.root position.1)),
    Finset.mem_univ _⟩

/-- A displayed side-slot dart lies on the selected interior corridor face. -/
theorem pointwiseLocalPlacementSideDart_internal
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    dartOrbitFace formation.annular.RS
        (faceCycleDart formation.annular.RS placement.root position.1) ∈
      formation.annular.cellulation.interiorFaces := by
  rw [dartOrbitFace_faceCycleDart, placement.root_face]
  exact corridor.face_internal interior.center

/-- The opposite-dart face is not the selected corridor centre. -/
theorem pointwiseLocalPlacementSideFace_val_ne_center
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    (pointwiseLocalPlacementSideFace placement position).1 ≠
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center).1 := by
  let sideDart := faceCycleDart formation.annular.RS placement.root position.1
  intro hsame
  apply InteriorFace.dartOrbitFace_ne_alpha formation sideDart
    (pointwiseLocalPlacementSideDart_internal
      (corridor := corridor) placement position)
  calc
    dartOrbitFace formation.annular.RS sideDart =
        dartOrbitFace formation.annular.RS placement.root :=
      dartOrbitFace_faceCycleDart formation.annular.RS placement.root position.1
    _ = ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1 := placement.root_face
    _ = dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha sideDart) := hsame.symm

/-- A literal side face is adjacent to its selected corridor centre. -/
theorem pointwiseLocalPlacementSideFace_adjacent_center
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    (interiorDualGraph (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center)
        (pointwiseLocalPlacementSideFace placement position) := by
  let sideDart := faceCycleDart formation.annular.RS placement.root position.1
  refine interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary formation.annular.RS)
    (Finset.univ : Finset (OrbitFace formation.annular.RS))
    (orbitFace_incidence_le_two formation.annular.RS)
    (e := formation.annular.RS.edgeOf sideDart) ?_ ?_ ?_
  · intro hsame
    apply pointwiseLocalPlacementSideFace_val_ne_center
      (corridor := corridor) placement position
    exact hsame.symm
  · change formation.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary formation.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
    have hside := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      formation.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hside
    exact hside
  · change formation.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary formation.annular.RS
        (dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha sideDart))
    rw [← formation.annular.RS.edge_alpha sideDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha sideDart)

/-- Boundary cleanliness keeps the side face annular-interior. -/
theorem pointwiseLocalPlacementSideFace_internal
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    (pointwiseLocalPlacementSideFace placement position).1 ∈
      formation.annular.cellulation.interiorFaces :=
  corridor.neighbor_internal interior.center
    (pointwiseLocalPlacementSideFace placement position)
    (pointwiseLocalPlacementSideFace_adjacent_center
      (corridor := corridor) placement position)

/-- A side-slot edge differs from both pointwise corridor rungs. -/
theorem pointwiseLocalPlacementSideEdge_ne_rungs
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    formation.annular.RS.edgeOf
        (faceCycleDart formation.annular.RS placement.root position.1) ≠
        pointwiseRungEdge
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          hlocal interior.incoming ∧
      formation.annular.RS.edgeOf
        (faceCycleDart formation.annular.RS placement.root position.1) ≠
        pointwiseRungEdge
          corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          hlocal interior.outgoing := by
  have hposition := (PointwiseInternalHexRungPlacement.mem_sidePositions_iff
    placement position.1).1 position.2
  have hinjective := InteriorFace.faceCycleEdge_injective formation placement.root
    (by
      rw [placement.root_face]
      exact corridor.face_internal interior.center)
  constructor
  · intro hedge
    apply hposition.1
    apply hinjective
    exact hedge.trans placement.incoming_edge.symm
  · intro hedge
    apply hposition.2
    apply hinjective
    exact hedge.trans placement.outgoing_edge.symm

/-- A non-rung side face is not the next corridor centre. -/
theorem pointwiseLocalPlacementSideFace_val_ne_nextCenter
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions}) :
    (pointwiseLocalPlacementSideFace placement position).1 ≠
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let sideDart := faceCycleDart formation.annular.RS placement.root position.1
  have hsideBoundary : formation.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      formation.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hsideInterior : formation.annular.RS.edgeOf sideDart ∈
      interiorEdgeSupport (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS)) := by
    apply InteriorFace.edge_mem_interiorEdgeSupport formation sideDart
    exact pointwiseLocalPlacementSideDart_internal
      (corridor := corridor) placement position
  intro hsame
  have hnextBoundary : formation.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha sideDart)
    rw [formation.annular.RS.edge_alpha sideDart] at hraw
    change formation.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary formation.annular.RS
        (pointwiseLocalPlacementSideFace placement position).1 at hraw
    rw [hsame] at hraw
    exact hraw
  have hshared : formation.annular.RS.edgeOf sideDart ∈
      sharedInteriorEdges (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS))
        (skeleton.faceAt interior.outgoing.left).1
        (skeleton.faceAt interior.outgoing.right).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).2
    refine ⟨hsideInterior, ?_, ?_⟩
    · simpa [skeleton] using hsideBoundary
    · simpa [skeleton, nextCorridorInterior] using hnextBoundary
  have hrung := pointwiseRungEdge_eq_of_mem skeleton hlocal
    interior.outgoing hshared
  exact (pointwiseLocalPlacementSideEdge_ne_rungs
    (corridor := corridor) placement position).2 hrung.symm

/-- The face opposite the literal outgoing rung is the next corridor face. -/
theorem pointwiseLocalOutgoingAlphaFace_eq_nextCenter
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior) :
    dartOrbitFace formation.annular.RS (formation.annular.RS.alpha
        (faceCycleDart formation.annular.RS placement.root
          placement.outgoingPosition)) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let outgoingDart := faceCycleDart formation.annular.RS placement.root
    placement.outgoingPosition
  have houtgoingFace : dartOrbitFace formation.annular.RS outgoingDart =
      (skeleton.faceAt interior.center).1 := by
    exact (dartOrbitFace_faceCycleDart formation.annular.RS placement.root
      placement.outgoingPosition).trans placement.root_face
  have houtgoingInternal : dartOrbitFace formation.annular.RS outgoingDart ∈
      formation.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal interior.center
  have hedgeNext : formation.annular.RS.edgeOf outgoingDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 := by
    change faceCycleEdge formation.annular.RS placement.root
      placement.outgoingPosition ∈ orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1
    rw [placement.outgoing_edge]
    simpa [nextCorridorInterior] using
      pointwiseRungEdge_mem_right skeleton hlocal interior.outgoing
  apply InteriorFace.alpha_face_eq_of_mem_other formation outgoingDart
    houtgoingInternal
    (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 hedgeNext
  rw [houtgoingFace]
  intro hfaces
  have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
  have hvalues := congrArg Fin.val hindices
  change interior.center.val = interior.center.val + 1 at hvalues
  omega

/-- The four literal side slots reach four different face orbits. -/
theorem pointwiseLocalPlacementSideFace_injective
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior) :
    Function.Injective (pointwiseLocalPlacementSideFace placement) := by
  intro left right hfaces
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let leftDart := faceCycleDart formation.annular.RS placement.root left.1
  let rightDart := faceCycleDart formation.annular.RS placement.root right.1
  have hleftBoundary : formation.annular.RS.edgeOf leftDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      formation.annular.RS leftDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hrightBoundary : formation.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      formation.annular.RS rightDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hleftAcross : formation.annular.RS.edgeOf leftDart ∈
      orbitFaceBoundary formation.annular.RS
        (pointwiseLocalPlacementSideFace placement left).1 := by
    change formation.annular.RS.edgeOf leftDart ∈ orbitFaceBoundary
      formation.annular.RS
        (dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha leftDart))
    rw [← formation.annular.RS.edge_alpha leftDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha leftDart)
  have hfacesVal : dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha leftDart) =
      dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha rightDart) :=
    congrArg Subtype.val hfaces
  have hrightAcross : formation.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary formation.annular.RS
        (pointwiseLocalPlacementSideFace placement left).1 := by
    change formation.annular.RS.edgeOf rightDart ∈ orbitFaceBoundary
      formation.annular.RS
        (dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha leftDart))
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha rightDart)
    rw [formation.annular.RS.edge_alpha rightDart] at hraw
    rw [hfacesVal]
    exact hraw
  have hleftShared : formation.annular.RS.edgeOf leftDart ∈
      sharedInteriorEdges (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS))
        (skeleton.faceAt interior.center).1
        (pointwiseLocalPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport formation leftDart
      (pointwiseLocalPlacementSideDart_internal
        (corridor := corridor) placement left), hleftBoundary, hleftAcross⟩
  have hrightShared : formation.annular.RS.edgeOf rightDart ∈
      sharedInteriorEdges (orbitFaceBoundary formation.annular.RS)
        (Finset.univ : Finset (OrbitFace formation.annular.RS))
        (skeleton.faceAt interior.center).1
        (pointwiseLocalPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport formation rightDart
      (pointwiseLocalPlacementSideDart_internal
        (corridor := corridor) placement right), hrightBoundary, hrightAcross⟩
  have hcard := card_le_one_of_interior formation.annular.cellulation hinterior
    (corridor.face_internal interior.center)
    (pointwiseLocalPlacementSideFace_internal
      (corridor := corridor) placement left)
    (pointwiseLocalPlacementSideFace_adjacent_center
      (corridor := corridor) placement left)
  apply Subtype.ext
  apply InteriorFace.faceCycleEdge_injective formation placement.root
    (by rw [placement.root_face]; exact corridor.face_internal interior.center)
  change formation.annular.RS.edgeOf leftDart =
    formation.annular.RS.edgeOf rightDart
  exact (Finset.card_le_one_iff.1 hcard) hleftShared hrightShared

/-- The side slot immediately before the outgoing rung meets the next centre. -/
theorem pointwiseLocalPlacementSideFace_adjacent_next_of_before_outgoing
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions})
    (hsuccessor : placement.outgoingPosition.val ≡ position.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).Adj
        (pointwiseLocalPlacementSideFace placement position)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center) := by
  let sideDart := faceCycleDart formation.annular.RS placement.root position.1
  let outgoingDart := faceCycleDart formation.annular.RS placement.root
    placement.outgoingPosition
  have hdarts : outgoingDart = formation.annular.RS.phi sideDart :=
    faceCycleDart_successor_of_modEq formation.annular.RS placement.root
      placement.orbit_card position.1 placement.outgoingPosition hsuccessor
  have houtgoingOpposite := pointwiseLocalOutgoingAlphaFace_eq_nextCenter
    (corridor := corridor) hnext placement
  have hcornerNe : dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha sideDart) ≠ dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha (formation.annular.RS.phi sideDart)) := by
    intro hfaces
    apply pointwiseLocalPlacementSideFace_val_ne_nextCenter
      (corridor := corridor) hnext placement position
    change dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha sideDart) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1
    calc
      dartOrbitFace formation.annular.RS (formation.annular.RS.alpha sideDart) =
          dartOrbitFace formation.annular.RS
            (formation.annular.RS.alpha
              (formation.annular.RS.phi sideDart)) := hfaces
      _ = dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha outgoingDart) := by rw [← hdarts]
      _ = ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1 := houtgoingOpposite
  have hcornerCard : (formation.annular.RS.dartsAt
      (formation.annular.RS.vertOf
        (formation.annular.RS.alpha sideDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three formation
    exact pointwiseLocalPlacementSideFace_internal
      (corridor := corridor) placement position
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner formation.annular.RS
    (InteriorFace.vertexRotationCyclic formation) sideDart hcornerCard hcornerNe
  have hnextEq :
      (⟨dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha (formation.annular.RS.phi sideDart)),
        Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace formation.annular.RS))) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center) := by
    apply Subtype.ext
    rw [← hdarts]
    exact houtgoingOpposite
  rw [← hnextEq]
  exact hadj

/-- The side slot immediately after the outgoing rung also meets the next centre. -/
theorem pointwiseLocalPlacementSideFace_adjacent_next_of_after_outgoing
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior)
    (position : {position // position ∈ placement.sidePositions})
    (hsuccessor : position.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))).Adj
        (pointwiseLocalPlacementSideFace placement position)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center) := by
  let outgoingDart := faceCycleDart formation.annular.RS placement.root
    placement.outgoingPosition
  let sideDart := faceCycleDart formation.annular.RS placement.root position.1
  have hdarts : sideDart = formation.annular.RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq formation.annular.RS placement.root
      placement.orbit_card placement.outgoingPosition position.1 hsuccessor
  have houtgoingOpposite := pointwiseLocalOutgoingAlphaFace_eq_nextCenter
    (corridor := corridor) hnext placement
  have hcornerNe : dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha outgoingDart) ≠
        dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha
            (formation.annular.RS.phi outgoingDart)) := by
    intro hfaces
    apply pointwiseLocalPlacementSideFace_val_ne_nextCenter
      (corridor := corridor) hnext placement position
    change dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha sideDart) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1
    rw [hdarts]
    exact hfaces.symm.trans houtgoingOpposite
  have hcornerCard : (formation.annular.RS.dartsAt
      (formation.annular.RS.vertOf
        (formation.annular.RS.alpha outgoingDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three formation
    rw [houtgoingOpposite]
    exact corridor.face_internal (nextCorridorInterior interior hnext).center
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner formation.annular.RS
    (InteriorFace.vertexRotationCyclic formation) outgoingDart hcornerCard hcornerNe
  have hsideEq :
      (⟨dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha
            (formation.annular.RS.phi outgoingDart)), Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace formation.annular.RS))) =
      pointwiseLocalPlacementSideFace placement position := by
    apply Subtype.ext
    change dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha
          (formation.annular.RS.phi outgoingDart)) =
      dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha sideDart)
    rw [← hdarts]
  have hnextEq :
      (⟨dartOrbitFace formation.annular.RS
          (formation.annular.RS.alpha outgoingDart), Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace formation.annular.RS))) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center) :=
    Subtype.ext houtgoingOpposite
  rw [← hsideEq, ← hnextEq]
  exact hadj.symm

/-- Forget the source slots while retaining the exact local two-rail geometry. -/
noncomputable def PointwiseSourceLocalLayerPairWitness.toLocalLayerPair
    {data : AnnularBoundaryData G 5}
    {formation : Formation data} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength}
    {hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (witness : PointwiseSourceLocalLayerPairWitness formation corridor hlocal
      leftInterior hnext) :
    Formation.LocalLayerPair formation corridor leftInterior hnext := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  refine {
    firstFace := pointwiseLocalPlacementSideFace
      witness.placement witness.before
    secondFace := pointwiseLocalPlacementSideFace
      witness.placement witness.after
    first_ne_second := ?_
    center_ne_nextCenter := ?_
    first_adjacent_center :=
      (pointwiseLocalPlacementSideFace_adjacent_center
        (corridor := corridor) witness.placement witness.before).symm
    center_adjacent_second :=
      pointwiseLocalPlacementSideFace_adjacent_center
        (corridor := corridor) witness.placement witness.after
    first_adjacent_nextCenter :=
      pointwiseLocalPlacementSideFace_adjacent_next_of_before_outgoing
        (corridor := corridor) hnext witness.placement witness.before
        witness.outgoing_after_before
    nextCenter_adjacent_second :=
      (pointwiseLocalPlacementSideFace_adjacent_next_of_after_outgoing
        (corridor := corridor) hnext witness.placement witness.after
        witness.after_after_outgoing).symm
    first_internal := pointwiseLocalPlacementSideFace_internal
      (corridor := corridor) witness.placement witness.before
    second_internal := pointwiseLocalPlacementSideFace_internal
      (corridor := corridor) witness.placement witness.after }
  · intro hfaces
    exact witness.before_ne_after
      (pointwiseLocalPlacementSideFace_injective
        (corridor := corridor) hinterior witness.placement hfaces)
  · intro hfaces
    have hindices := skeleton.faceAt_injective hfaces
    have hvalues := congrArg Fin.val hindices
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega

/-- The corrected pointwise source witness therefore supplies the local layer
pair consumed by the Cell transition. -/
theorem exists_pointwiseLocalLayerPair_of_interiorUnique
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (Formation.LocalLayerPair formation corridor leftInterior hnext) := by
  let hlocal := boundaryCleanCorridor_consecutiveRungUnique formation.annular
    hinterior corridor
  let witness := pointwiseSourceLocalLayerPairWitness formation corridor hlocal
    leftInterior hnext
  exact ⟨witness.toLocalLayerPair hinterior⟩

end LocalLayerFormation

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
