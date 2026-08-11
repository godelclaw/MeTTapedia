import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRungPlacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebCorridorLayer

/-!
# Source-derived Cell-3 layer interfaces

The Cell-3 corridor has genuine simple interior faces but open-tangle hole
stubs at its boundary.  This file constructs the local rail faces directly
from the six-edge boundary of each selected corridor face.  It therefore
uses local simple-face incidence at each step, rather than importing a global
two-sidedness assertion that would be false for the carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

/-- The face across one non-rung position of a locally placed Cell-3
hexagon.  Its definition is the literal face of the opposite dart; the
following lemmas prove the incidence properties needed for a rail. -/
noncomputable def localPlacementSideFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)) :=
  ⟨dartOrbitFace web.annular.RS
      (web.annular.RS.alpha
        (faceCycleDart web.annular.RS placement.root position.1)),
    Finset.mem_univ _⟩

/-- The dart represented by any slot of a local placement lies on the chosen
source corridor face, hence on an annular-interior face. -/
theorem localPlacementSideDart_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    dartOrbitFace web.annular.RS
        (faceCycleDart web.annular.RS placement.root position.1) ∈
      web.annular.cellulation.interiorFaces := by
  rw [dartOrbitFace_faceCycleDart, placement.root_face]
  exact corridor.face_internal interior.center

/-- A local side face cannot be the chosen corridor centre: the source face
is simple, so a facial dart and its opposite belong to different faces. -/
theorem localPlacementSideFace_val_ne_center
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (localPlacementSideFace placement position).1 ≠
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center).1 := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  intro hsame
  change dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center).1 at hsame
  apply InteriorFace.dartOrbitFace_ne_alpha web sideDart
    (localPlacementSideDart_internal (corridor := corridor) placement position)
  calc
    dartOrbitFace web.annular.RS sideDart =
        dartOrbitFace web.annular.RS placement.root := by
          exact dartOrbitFace_faceCycleDart web.annular.RS placement.root
            position.1
    _ = ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1 := placement.root_face
    _ = dartOrbitFace web.annular.RS
        (web.annular.RS.alpha sideDart) := hsame.symm

/-- A source-local side face is genuinely adjacent to its corridor centre.
The witnessing edge is interior because its simple source face and opposite
dart exhibit its two distinct incident face orbits. -/
theorem localPlacementSideFace_adjacent_center
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center)
        (localPlacementSideFace placement position) := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  refine interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (orbitFace_incidence_le_two web.annular.RS)
    (e := web.annular.RS.edgeOf sideDart) ?_ ?_ ?_
  · intro hsame
    apply localPlacementSideFace_val_ne_center (corridor := corridor) placement position
    exact hsame.symm
  · change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
    have hside := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hside
    exact hside
  · change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
    rw [← web.annular.RS.edge_alpha sideDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart)

/-- Radius-one cleanliness of the source corridor keeps every local side
face away from both named holes. -/
theorem localPlacementSideFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (localPlacementSideFace placement position).1 ∈
      web.annular.cellulation.interiorFaces := by
  exact corridor.neighbor_internal interior.center
    (localPlacementSideFace placement position)
    (localPlacementSideFace_adjacent_center (corridor := corridor) placement position)

/-- A retained side slot is genuinely different from each of the two rung
positions of its placed hexagon.  This is the ordered version of the
four-slot interface, obtained from the source face's simple boundary rather
than a global two-sidedness assumption. -/
theorem localPlacementSideEdge_ne_rungs
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS placement.root position.1) ≠
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).rungEdge hunique interior.incoming ∧
      web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS placement.root position.1) ≠
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).rungEdge hunique interior.outgoing := by
  have hposition :=
    (mem_placementSidePositions_iff placement position.1).1 position.2
  have hinjective := InteriorFace.faceCycleEdge_injective web placement.root
    (by
      rw [placement.root_face]
      exact corridor.face_internal interior.center)
  constructor
  · intro hedge
    apply hposition.1
    apply hinjective
    calc
      faceCycleEdge web.annular.RS placement.root position.1 =
          web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS placement.root position.1) := rfl
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).rungEdge hunique interior.incoming := hedge
      _ = faceCycleEdge web.annular.RS placement.root
          placement.incomingPosition := placement.incoming_edge.symm
  · intro hedge
    apply hposition.2
    apply hinjective
    calc
      faceCycleEdge web.annular.RS placement.root position.1 =
          web.annular.RS.edgeOf
            (faceCycleDart web.annular.RS placement.root position.1) := rfl
      _ = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).rungEdge hunique interior.outgoing := hedge
      _ = faceCycleEdge web.annular.RS placement.root
          placement.outgoingPosition := placement.outgoing_edge.symm

/-- The face across a side slot of an internal source hexagon cannot be the
next corridor face.  If it were, that side edge would be the canonical
outgoing rung, contradicting that the slot survived rung deletion. -/
theorem localPlacementSideFace_val_ne_nextCenter
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (localPlacementSideFace placement position).1 ≠
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  have hsideBoundary : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hsideInterior : web.annular.RS.edgeOf sideDart ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
    apply InteriorFace.edge_mem_interiorEdgeSupport web sideDart
    exact localPlacementSideDart_internal (corridor := corridor)
      placement position
  intro hsame
  change dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart) =
      (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 at hsame
  have hnextBoundary : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart)
    rw [web.annular.RS.edge_alpha sideDart, hsame] at hraw
    exact hraw
  have hshared : web.annular.RS.edgeOf sideDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt interior.outgoing.left).1
        (skeleton.faceAt interior.outgoing.right).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    refine ⟨hsideInterior, ?_, ?_⟩
    · simpa [skeleton] using hsideBoundary
    · simpa [skeleton, nextCorridorInterior] using hnextBoundary
  have hrung := skeleton.rungEdge_eq_of_shared hunique interior.outgoing hshared
  exact (localPlacementSideEdge_ne_rungs (corridor := corridor)
    placement position).2 hrung.symm

/-- The face opposite a real outgoing rung is exactly the next source
corridor face.  This is the local replacement for the global two-sided-face
lookup used by the closed cubic corridor calculus. -/
theorem localOutgoingAlphaFace_eq_nextCenter
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior) :
    dartOrbitFace web.annular.RS (web.annular.RS.alpha
        (faceCycleDart web.annular.RS placement.root
          placement.outgoingPosition)) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let outgoingDart := faceCycleDart web.annular.RS placement.root
    placement.outgoingPosition
  have houtgoingFace : dartOrbitFace web.annular.RS outgoingDart =
      (skeleton.faceAt interior.center).1 := by
    calc
      dartOrbitFace web.annular.RS outgoingDart =
          dartOrbitFace web.annular.RS placement.root := by
            exact dartOrbitFace_faceCycleDart web.annular.RS placement.root
              placement.outgoingPosition
      _ = (skeleton.faceAt interior.center).1 := placement.root_face
  have houtgoingInternal : dartOrbitFace web.annular.RS outgoingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal interior.center
  have hedgeNext : web.annular.RS.edgeOf outgoingDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 := by
    change faceCycleEdge web.annular.RS placement.root
      placement.outgoingPosition ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt (nextCorridorInterior interior hnext).center).1
    rw [placement.outgoing_edge]
    simpa [nextCorridorInterior] using
      skeleton.rungEdge_mem_right hunique interior.outgoing
  apply InteriorFace.alpha_face_eq_of_mem_other web outgoingDart
    houtgoingInternal
    (skeleton.faceAt (nextCorridorInterior interior hnext).center).1 hedgeNext
  rw [houtgoingFace]
  intro hfaces
  have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
  have hvalues := congrArg Fin.val hindices
  change interior.center.val = interior.center.val + 1 at hvalues
  omega

/-- The four surviving side slots of a locally placed Cell-3 hexagon reach
four different face orbits.  The source corridor's pairwise-unique shared
interior-edge certificate gives the same width-four conclusion as the closed
cubic calculation, but only for the actual local source faces. -/
theorem localPlacementSideFace_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior) :
    Function.Injective (localPlacementSideFace placement) := by
  intro left right hfaces
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let leftDart := faceCycleDart web.annular.RS placement.root left.1
  let rightDart := faceCycleDart web.annular.RS placement.root right.1
  have hleftBoundary : web.annular.RS.edgeOf leftDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS leftDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hrightBoundary : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS rightDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hleftAcross : web.annular.RS.edgeOf leftDart ∈
      orbitFaceBoundary web.annular.RS
        (localPlacementSideFace placement left).1 := by
    change web.annular.RS.edgeOf leftDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart))
    rw [← web.annular.RS.edge_alpha leftDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart)
  have hfacesVal : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart) =
      dartOrbitFace web.annular.RS
        (web.annular.RS.alpha rightDart) := by
    exact congrArg Subtype.val hfaces
  have hrightAcross : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS
        (localPlacementSideFace placement left).1 := by
    change web.annular.RS.edgeOf rightDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart))
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha rightDart)
    rw [web.annular.RS.edge_alpha rightDart] at hraw
    rw [hfacesVal]
    exact hraw
  have hleftShared : web.annular.RS.edgeOf leftDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt interior.center).1
        (localPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport web leftDart
      (localPlacementSideDart_internal (corridor := corridor) placement left),
      hleftBoundary, hleftAcross⟩
  have hrightShared : web.annular.RS.edgeOf rightDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt interior.center).1
        (localPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport web rightDart
      (localPlacementSideDart_internal (corridor := corridor) placement right),
      hrightBoundary, hrightAcross⟩
  have hcard := hunique (skeleton.faceAt interior.center).1
    (skeleton.faceAt interior.center).2
    (localPlacementSideFace placement left).1
    (localPlacementSideFace placement left).2 (by
      intro hsame
      exact localPlacementSideFace_val_ne_center (corridor := corridor)
        placement left hsame.symm)
  apply Subtype.ext
  apply InteriorFace.faceCycleEdge_injective web placement.root
    (by
      rw [placement.root_face]
      exact corridor.face_internal interior.center)
  change web.annular.RS.edgeOf leftDart = web.annular.RS.edgeOf rightDart
  exact (Finset.card_le_one_iff.1 hcard) hleftShared hrightShared

/-- The retained side slot immediately before the outgoing rung is a real
rail step into the next corridor hexagon.  Only the two local cubic corners
used by the step are invoked. -/
theorem localPlacementSideFace_adjacent_next_of_before_outgoing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : placement.outgoingPosition.val ≡ position.1.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (localPlacementSideFace placement position)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center) := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  let outgoingDart := faceCycleDart web.annular.RS placement.root
    placement.outgoingPosition
  have hdarts : outgoingDart = web.annular.RS.phi sideDart :=
    faceCycleDart_successor_of_modEq web.annular.RS placement.root
      placement.orbit_card position.1 placement.outgoingPosition hsuccessor
  have houtgoingOpposite := localOutgoingAlphaFace_eq_nextCenter
    (corridor := corridor) hnext placement
  have hcornerNe : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart) ≠ dartOrbitFace web.annular.RS
        (web.annular.RS.alpha (web.annular.RS.phi sideDart)) := by
    intro hfaces
    apply localPlacementSideFace_val_ne_nextCenter (corridor := corridor)
      hnext placement position
    change dartOrbitFace web.annular.RS
        (web.annular.RS.alpha sideDart) =
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1
    calc
      dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart) =
          dartOrbitFace web.annular.RS
            (web.annular.RS.alpha (web.annular.RS.phi sideDart)) := hfaces
      _ = dartOrbitFace web.annular.RS
          (web.annular.RS.alpha outgoingDart) := by rw [← hdarts]
      _ = ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1 := houtgoingOpposite
  have hcornerCard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha sideDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three web
    change (localPlacementSideFace placement position).1 ∈
      web.annular.cellulation.interiorFaces
    exact localPlacementSideFace_internal (corridor := corridor)
      placement position
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
    (InteriorFace.vertexRotationCyclic web) sideDart hcornerCard hcornerNe
  have hnextEq :
      (⟨dartOrbitFace web.annular.RS
          (web.annular.RS.alpha (web.annular.RS.phi sideDart)),
        Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center) := by
    apply Subtype.ext
    rw [← hdarts]
    exact houtgoingOpposite
  rw [← hnextEq]
  exact hadj

/-- The retained side slot immediately after the outgoing rung is the other
local rail step into the next corridor hexagon. -/
theorem localPlacementSideFace_adjacent_next_of_after_outgoing
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {interior : CorridorInterior blockLength}
    (hnext : interior.center.val + 2 < blockLength)
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior)
    (position : {position // position ∈ placementSidePositions placement})
    (hsuccessor : position.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6]) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (localPlacementSideFace placement position)
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center) := by
  let outgoingDart := faceCycleDart web.annular.RS placement.root
    placement.outgoingPosition
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  have hdarts : sideDart = web.annular.RS.phi outgoingDart :=
    faceCycleDart_successor_of_modEq web.annular.RS placement.root
      placement.orbit_card placement.outgoingPosition position.1 hsuccessor
  have houtgoingOpposite := localOutgoingAlphaFace_eq_nextCenter
    (corridor := corridor) hnext placement
  have hcornerNe : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha outgoingDart) ≠ dartOrbitFace web.annular.RS
        (web.annular.RS.alpha (web.annular.RS.phi outgoingDart)) := by
    intro hfaces
    apply localPlacementSideFace_val_ne_nextCenter (corridor := corridor)
      hnext placement position
    change dartOrbitFace web.annular.RS
        (web.annular.RS.alpha sideDart) =
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1
    rw [hdarts]
    exact hfaces.symm.trans houtgoingOpposite
  have hcornerCard : (web.annular.RS.dartsAt
      (web.annular.RS.vertOf (web.annular.RS.alpha outgoingDart))).card = 3 := by
    apply InteriorFace.dartsAt_card_eq_three web
    rw [houtgoingOpposite]
    exact corridor.face_internal (nextCorridorInterior interior hnext).center
  have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
    (InteriorFace.vertexRotationCyclic web) outgoingDart hcornerCard hcornerNe
  have hsideEq :
      (⟨dartOrbitFace web.annular.RS
          (web.annular.RS.alpha (web.annular.RS.phi outgoingDart)),
        Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) =
      localPlacementSideFace placement position := by
    apply Subtype.ext
    change dartOrbitFace web.annular.RS
        (web.annular.RS.alpha (web.annular.RS.phi outgoingDart)) =
        dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart)
    rw [← hdarts]
  have hnextEq :
      (⟨dartOrbitFace web.annular.RS
          (web.annular.RS.alpha outgoingDart), Finset.mem_univ _⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center) :=
    Subtype.ext houtgoingOpposite
  rw [← hsideEq, ← hnextEq]
  exact hadj.symm

/-- Two consecutive internal Cell-3 corridor faces construct their local
layer pair directly.  The two rails are selected from the actual source face
slots immediately flanking the outgoing rung; no caller supplies exterior
faces or a synthetic transversal. -/
theorem exists_localLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (LocalLayerPair web corridor leftInterior hnext) := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let placement := localInternalHexRungPlacement corridor hunique leftInterior
  have hnonadjacent : placement.rungType ≠ HexRungType.adjacent :=
    GoertzelV24ClosedWebAtGoodWord.Instance.InternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor hunique leftInterior placement
  rcases exists_two_hexSidePositions_flanking_outgoing
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with
    ⟨before6, after6, hbeforeAfter, hbeforeMod, hafterMod⟩
  let before := placementSidePositionOfSix placement before6
  let after := placementSidePositionOfSix placement after6
  have hbeforeNeAfter : before ≠ after := by
    intro heq
    apply hbeforeAfter
    apply Subtype.ext
    have hvalues := congrArg (fun position => position.1.val) heq
    exact Fin.ext hvalues
  have hbeforeActual : placement.outgoingPosition.val ≡
      before.1.val + 1 [MOD 6] := by
    simpa [before, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  have hafterActual : after.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [after, placementSidePositionOfSix, placementPositionOfSix,
      InternalHexRungPlacement.outgoingPosition6] using hafterMod
  refine ⟨{
    firstFace := localPlacementSideFace placement before
    secondFace := localPlacementSideFace placement after
    first_ne_second := ?_
    center_ne_nextCenter := ?_
    first_adjacent_center :=
      localPlacementSideFace_adjacent_center (corridor := corridor)
        placement before |>.symm
    center_adjacent_second :=
      localPlacementSideFace_adjacent_center (corridor := corridor)
        placement after
    first_adjacent_nextCenter :=
      localPlacementSideFace_adjacent_next_of_before_outgoing
        (corridor := corridor) hnext placement before hbeforeActual
    nextCenter_adjacent_second :=
      localPlacementSideFace_adjacent_next_of_after_outgoing
        (corridor := corridor) hnext placement after hafterActual |>.symm
    first_internal := localPlacementSideFace_internal (corridor := corridor)
      placement before
    second_internal := localPlacementSideFace_internal (corridor := corridor)
      placement after }⟩
  · intro hfaces
    exact hbeforeNeAfter
      (localPlacementSideFace_injective (corridor := corridor)
        placement hfaces)
  · intro hfaces
    have hindices := skeleton.faceAt_injective hfaces
    have hvalues := congrArg Fin.val hindices
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega

/-- The canonical Cell-3 local layer pair generated by the real corridor
geometry.  It is a choice only from the finite, source-proved placement and
flanking-slot witnesses above. -/
noncomputable def localLayerPairOfCorridor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    LocalLayerPair web corridor leftInterior hnext :=
  Classical.choice (exists_localLayerPair corridor hunique leftInterior hnext)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
