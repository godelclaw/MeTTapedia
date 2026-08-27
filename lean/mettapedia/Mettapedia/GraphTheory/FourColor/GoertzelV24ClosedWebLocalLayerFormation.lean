import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularInteriorFaceUniqueness
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
open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24DualPathTransversal
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

/-- The actual finite Cell-3 data from which a local layer pair is formed.
Keeping the placement and its two flanking slots alongside the resulting
faces is what lets later separator arguments read the four primal cut edges
from the source face, instead of treating a bare dual adjacency as if it
remembered its witnessing edge. -/
structure SourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5}
    (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) where
  placement : InternalHexRungPlacement
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    hunique leftInterior
  before : {position // position ∈ placementSidePositions placement}
  after : {position // position ∈ placementSidePositions placement}
  before_ne_after : before ≠ after
  outgoing_after_before : placement.outgoingPosition.val ≡
    before.1.val + 1 [MOD 6]
  after_after_outgoing : after.1.val ≡
    placement.outgoingPosition.val + 1 [MOD 6]

/-- The source-local Cell witness with the dependency corrected to the
pointwise corridor receipt.  Its finite data are identical to the historical
record, but neither its formation nor its placement carries a colouring or a
global face-intersection hypothesis. -/
structure PointwiseSourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5}
    (formation : Formation data) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) where
  placement : PointwiseInternalHexRungPlacement
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    hlocal leftInterior
  before : {position // position ∈ placement.sidePositions}
  after : {position // position ∈ placement.sidePositions}
  before_ne_after : before ≠ after
  outgoing_after_before : placement.outgoingPosition.val ≡
    before.1.val + 1 [MOD 6]
  after_after_outgoing : after.1.val ≡
    placement.outgoingPosition.val + 1 [MOD 6]

/-- The corrected source witness exists directly from formation geometry and
the consecutive-rung receipt. -/
theorem exists_pointwiseSourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (PointwiseSourceLocalLayerPairWitness formation corridor hlocal
      leftInterior hnext) := by
  let placement := Formation.localPointwiseInternalHexRungPlacement formation
    corridor hlocal leftInterior
  have hnonadjacent : placement.rungType ≠ HexRungType.adjacent :=
    GoertzelV24ClosedWebAtGoodWord.Formation.PointwiseInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      formation corridor hlocal leftInterior placement
  rcases exists_two_hexSidePositions_flanking_outgoing
      placement.incomingPosition6 placement.outgoingPosition6
      placement.positions6_ne hnonadjacent with
    ⟨before6, after6, hbeforeAfter, hbeforeMod, hafterMod⟩
  let before := placement.sidePositionOfSix before6
  let after := placement.sidePositionOfSix after6
  have hbeforeNeAfter : before ≠ after := by
    intro heq
    apply hbeforeAfter
    apply Subtype.ext
    have hvalues := congrArg (fun position => position.1.val) heq
    exact Fin.ext hvalues
  have hbeforeActual : placement.outgoingPosition.val ≡
      before.1.val + 1 [MOD 6] := by
    simpa [before, PointwiseInternalHexRungPlacement.sidePositionOfSix,
      PointwiseInternalHexRungPlacement.positionOfSix,
      PointwiseInternalHexRungPlacement.outgoingPosition6] using hbeforeMod
  have hafterActual : after.1.val ≡
      placement.outgoingPosition.val + 1 [MOD 6] := by
    simpa [after, PointwiseInternalHexRungPlacement.sidePositionOfSix,
      PointwiseInternalHexRungPlacement.positionOfSix,
      PointwiseInternalHexRungPlacement.outgoingPosition6] using hafterMod
  exact ⟨{
    placement := placement
    before := before
    after := after
    before_ne_after := hbeforeNeAfter
    outgoing_after_before := hbeforeActual
    after_after_outgoing := hafterActual }⟩

/-- Canonical corrected local witness. -/
noncomputable def pointwiseSourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    PointwiseSourceLocalLayerPairWitness formation corridor hlocal leftInterior
      hnext :=
  Classical.choice (exists_pointwiseSourceLocalLayerPairWitness formation
    corridor hlocal leftInterior hnext)

/-- The restricted annular interior-face property supplies the complete local
witness; the refuted hole-face pairs are never quantified over. -/
theorem exists_pointwiseSourceLocalLayerPairWitness_of_interiorUnique
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (PointwiseSourceLocalLayerPairWitness formation corridor
      (boundaryCleanCorridor_consecutiveRungUnique formation.annular hinterior
        corridor)
      leftInterior hnext) :=
  exists_pointwiseSourceLocalLayerPairWitness formation corridor
    (boundaryCleanCorridor_consecutiveRungUnique formation.annular hinterior
      corridor)
    leftInterior hnext

end LocalLayerFormation

end Formation

namespace Instance

namespace LocalLayerFormation

/-- Backward-compatible coloured spelling of the geometric source-layer
witness.  The record itself is carried by the inherited annular formation;
the colouring remains available to later Cell-3 consequences but is absent
from the local geometry ABI. -/
abbrev SourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :=
  Formation.LocalLayerFormation.SourceLocalLayerPairWitness web.toFormation
    corridor hunique leftInterior hnext

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

/-- The literal edge at a surviving Cell-3 side slot is the canonical primal
edge witnessing adjacency between the corridor centre and the corresponding
side face.  This keeps the local source geometry in the edge language used by
the closed-map dual-triangle classification. -/
theorem sharedInteriorEdge_localPlacementSideFace_eq
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
    sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        (localPlacementSideFace_adjacent_center
          (corridor := corridor) placement position) =
      web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS placement.root position.1) := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).2
  refine ⟨?_, ?_, ?_⟩
  · apply InteriorFace.edge_mem_interiorEdgeSupport web sideDart
    exact localPlacementSideDart_internal (corridor := corridor)
      placement position
  · have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
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

/-- A genuine side face of a boundary-clean Cell-3 corridor lies outside the
entire corridor axis, not merely outside its two immediate neighbours.  This
is the local-cubic counterpart of the clean-slab externality fact: a
nonconsecutive identification would create a forbidden corridor chord, while
an identification with either neighbour would turn the side edge into a
canonical rung.  Keeping the full statement here is necessary before two
local Cell-3 interfaces can be matched into a longer source transversal. -/
theorem localPlacementSideFace_ne_faceAt
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
    (position : {position // position ∈ placementSidePositions placement})
    (index : Fin blockLength) :
    localPlacementSideFace placement position ≠
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        index := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  have hcenterBoundary : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt interior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hraw
    exact hraw
  have hsideBoundary : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS (localPlacementSideFace placement position).1 := by
    change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
    rw [← web.annular.RS.edge_alpha sideDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart)
  have hsideInterior : web.annular.RS.edgeOf sideDart ∈ interiorEdgeSupport
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) := by
    apply InteriorFace.edge_mem_interiorEdgeSupport web sideDart
    exact localPlacementSideDart_internal (corridor := corridor)
      placement position
  have hposition :=
    (mem_placementSidePositions_iff placement position.1).1 position.2
  intro hsame
  have hadjIndex : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        (skeleton.faceAt interior.center) (skeleton.faceAt index) := by
    have hadj := localPlacementSideFace_adjacent_center (corridor := corridor)
      placement position
    simpa [skeleton, hsame] using hadj
  have hindexBoundary : web.annular.RS.edgeOf sideDart ∈
      orbitFaceBoundary web.annular.RS (skeleton.faceAt index).1 := by
    simpa [skeleton, hsame] using hsideBoundary
  have hindex_ne_center : index.val ≠ interior.center.val := by
    intro hval
    have hindex : index = interior.center := Fin.ext hval
    subst index
    exact hadjIndex.ne rfl
  rcases Nat.lt_or_gt_of_ne hindex_ne_center with hbefore | hafter
  · have hnotSeparated : ¬ index.val + 1 < interior.center.val := by
      intro hseparated
      exact (skeleton.separated_not_adjacent index interior.center hseparated)
        hadjIndex.symm
    have hpredecessorVal : interior.center.val = index.val + 1 := by
      omega
    have hpredecessor : index = interior.incoming.left := by
      apply Fin.ext
      change index.val = interior.center.val - 1
      have hcenterPositive := interior.center_pos
      omega
    have hshared : web.annular.RS.edgeOf sideDart ∈
        sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (skeleton.faceAt interior.incoming.left).1
          (skeleton.faceAt interior.incoming.right).1 := by
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).2
      refine ⟨hsideInterior, ?_, ?_⟩
      · simpa [hpredecessor] using hindexBoundary
      · simpa using hcenterBoundary
    have hrung := skeleton.rungEdge_eq_of_shared hunique interior.incoming hshared
    apply hposition.1
    apply InteriorFace.faceCycleEdge_injective web placement.root
      (by
        rw [placement.root_face]
        exact corridor.face_internal interior.center)
    calc
      faceCycleEdge web.annular.RS placement.root position.1 =
          web.annular.RS.edgeOf sideDart := rfl
      _ = skeleton.rungEdge hunique interior.incoming := hrung.symm
      _ = faceCycleEdge web.annular.RS placement.root
          placement.incomingPosition := placement.incoming_edge.symm
  · have hnotSeparated : ¬ interior.center.val + 1 < index.val := by
      intro hseparated
      exact (skeleton.separated_not_adjacent interior.center index hseparated)
        hadjIndex
    have hsuccessorVal : index.val = interior.center.val + 1 := by
      omega
    have hsuccessor : index = interior.outgoing.right := by
      apply Fin.ext
      exact hsuccessorVal
    have hshared : web.annular.RS.edgeOf sideDart ∈
        sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (skeleton.faceAt interior.outgoing.left).1
          (skeleton.faceAt interior.outgoing.right).1 := by
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).2
      refine ⟨hsideInterior, ?_, ?_⟩
      · simpa using hcenterBoundary
      · simpa [hsuccessor] using hindexBoundary
    have hrung := skeleton.rungEdge_eq_of_shared hunique interior.outgoing hshared
    apply hposition.2
    apply InteriorFace.faceCycleEdge_injective web placement.root
      (by
        rw [placement.root_face]
        exact corridor.face_internal interior.center)
    calc
      faceCycleEdge web.annular.RS placement.root position.1 =
          web.annular.RS.edgeOf sideDart := rfl
      _ = skeleton.rungEdge hunique interior.outgoing := hrung.symm
      _ = faceCycleEdge web.annular.RS placement.root
          placement.outgoingPosition := placement.outgoing_edge.symm

/-- **Source Cell-3 local geometry (not Fable flag L1).** The four literal side slots of a
boundary-clean Cell-3 hexagon are complete for external facial-dual
neighbours.  This is the local-simple-boundary replacement for the older
globally-two-sided slab lookup: an adjacent edge is located on the actual
six-cycle, its two canonical rungs are excluded by the externality premise,
and the opposite dart then identifies the requested neighbour. -/
theorem exists_localPlacementSideFace_eq_of_adjacent_external
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
    (neighbor : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hadj : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center) neighbor)
    (hexternal : ∀ index : Fin blockLength,
      neighbor ≠
        (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          index) :
    ∃ position : {position // position ∈ placementSidePositions placement},
      localPlacementSideFace placement position = neighbor := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let center := skeleton.faceAt interior.center
  rcases (interiorDualGraph_adj_iff (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))).1 hadj with
      ⟨hcenterNeighbor, edge, hedgeInterior, hedgeCenter, hedgeNeighbor⟩
  have hrootInternal : dartOrbitFace web.annular.RS placement.root ∈
      web.annular.cellulation.interiorFaces := by
    rw [placement.root_face]
    exact corridor.face_internal interior.center
  have hedgeRoot : edge ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS placement.root) := by
    rw [placement.root_face]
    simpa [center, skeleton] using hedgeCenter
  rcases InteriorFace.existsUnique_faceCycleEdge_eq web placement.root
      hrootInternal edge hedgeRoot with ⟨rawPosition, hrawEdge, _⟩
  have hedgeNeIncoming : edge ≠ skeleton.rungEdge hunique interior.incoming := by
    intro hedge
    have hcenterPredecessor : center.1 ≠
        (skeleton.faceAt interior.incoming.left).1 := by
      intro hfaces
      have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val = interior.center.val - 1 at hvalues
      have hcenterPositive := interior.center_pos
      omega
    have hedgePredecessor : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt interior.incoming.left).1 := by
      rw [hedge]
      exact skeleton.rungEdge_mem_left hunique interior.incoming
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS)
        center.2 (skeleton.faceAt interior.incoming.left).2 neighbor.2
        hcenterPredecessor hedgeCenter hedgePredecessor hedgeNeighbor
    rcases hcases with hcenter | hpredecessor
    · exact hcenterNeighbor hcenter.symm
    · exact hexternal interior.incoming.left (Subtype.ext hpredecessor)
  have hedgeNeOutgoing : edge ≠ skeleton.rungEdge hunique interior.outgoing := by
    intro hedge
    have hcenterSuccessor : center.1 ≠
        (skeleton.faceAt interior.outgoing.right).1 := by
      intro hfaces
      have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val = interior.center.val + 1 at hvalues
      omega
    have hedgeSuccessor : edge ∈ orbitFaceBoundary web.annular.RS
        (skeleton.faceAt interior.outgoing.right).1 := by
      rw [hedge]
      exact skeleton.rungEdge_mem_right hunique interior.outgoing
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS)
        center.2 (skeleton.faceAt interior.outgoing.right).2 neighbor.2
        hcenterSuccessor hedgeCenter hedgeSuccessor hedgeNeighbor
    rcases hcases with hcenter | hsuccessor
    · exact hcenterNeighbor hcenter.symm
    · exact hexternal interior.outgoing.right (Subtype.ext hsuccessor)
  let position : {position // position ∈ placementSidePositions placement} :=
    ⟨rawPosition, (mem_placementSidePositions_iff placement rawPosition).2 ⟨by
      intro hposition
      apply hedgeNeIncoming
      calc
        edge = faceCycleEdge web.annular.RS placement.root rawPosition := hrawEdge.symm
        _ = faceCycleEdge web.annular.RS placement.root placement.incomingPosition := by
          rw [hposition]
        _ = skeleton.rungEdge hunique interior.incoming := placement.incoming_edge,
      by
        intro hposition
        apply hedgeNeOutgoing
        calc
          edge = faceCycleEdge web.annular.RS placement.root rawPosition := hrawEdge.symm
          _ = faceCycleEdge web.annular.RS placement.root placement.outgoingPosition := by
            rw [hposition]
          _ = skeleton.rungEdge hunique interior.outgoing := placement.outgoing_edge⟩⟩
  refine ⟨position, ?_⟩
  apply Subtype.ext
  let sideDart := faceCycleDart web.annular.RS placement.root rawPosition
  have hsideInternal : dartOrbitFace web.annular.RS sideDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [dartOrbitFace_faceCycleDart, placement.root_face]
    exact corridor.face_internal interior.center
  have hsideCenter : dartOrbitFace web.annular.RS sideDart = center.1 := by
    rw [dartOrbitFace_faceCycleDart, placement.root_face]
  change dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart) = neighbor.1
  apply InteriorFace.alpha_face_eq_of_mem_other web sideDart hsideInternal
    neighbor.1
  · change faceCycleEdge web.annular.RS placement.root rawPosition ∈
      orbitFaceBoundary web.annular.RS neighbor.1
    rw [hrawEdge]
    exact hedgeNeighbor
  · intro hsame
    apply hcenterNeighbor
    exact hsideCenter.symm.trans hsame

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

/-- The rail from the side slot immediately before an outgoing rung to the
next corridor face crosses the third local edge at that corner. -/
theorem localPlacementThirdEdge_mem_sharedInteriorEdges_of_before_outgoing
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
    web.annular.RS.edgeOf
        (web.annular.RS.rho
          (web.annular.RS.phi
            (faceCycleDart web.annular.RS placement.root position.1))) ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (localPlacementSideFace placement position).1
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1 := by
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
  change web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi sideDart)) ∈
    sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1
  have hnextEq : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha (web.annular.RS.phi sideDart)) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := by
    rw [← hdarts]
    exact houtgoingOpposite
  have hthird := thirdEdge_mem_sharedInteriorEdges_at_locally_cubic_corner
    web.annular.RS (InteriorFace.vertexRotationCyclic web) sideDart
    hcornerCard hcornerNe
  rw [hnextEq] at hthird
  exact hthird

/-- The rail from the next corridor face to the side slot immediately after
an outgoing rung crosses the other third local edge at that rung. -/
theorem localPlacementThirdEdge_mem_sharedInteriorEdges_of_after_outgoing
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
    web.annular.RS.edgeOf
        (web.annular.RS.rho
          (web.annular.RS.phi
            (faceCycleDart web.annular.RS placement.root
              placement.outgoingPosition))) ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          (nextCorridorInterior interior hnext).center).1
        (localPlacementSideFace placement position).1 := by
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
  change web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi outgoingDart)) ∈
    sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
  have hnextEq : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha outgoingDart) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        (nextCorridorInterior interior hnext).center).1 := houtgoingOpposite
  have hsideEq : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha (web.annular.RS.phi outgoingDart)) =
      dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart) := by
    rw [← hdarts]
  have hthird := thirdEdge_mem_sharedInteriorEdges_at_locally_cubic_corner
    web.annular.RS (InteriorFace.vertexRotationCyclic web) outgoingDart
    hcornerCard hcornerNe
  rw [hnextEq, hsideEq] at hthird
  exact hthird

/-- Turn the literal source placement and its two slots into the local
two-rail interface.  This is deliberately a definition, not a forgetful
existence theorem: later cut calculations can keep referring to
`placement`, `before`, and `after`. -/
noncomputable def SourceLocalLayerPairWitness.toLocalLayerPair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    LocalLayerPair web corridor leftInterior hnext := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  refine {
    firstFace := localPlacementSideFace witness.placement witness.before
    secondFace := localPlacementSideFace witness.placement witness.after
    first_ne_second := ?_
    center_ne_nextCenter := ?_
    first_adjacent_center :=
      localPlacementSideFace_adjacent_center (corridor := corridor)
        witness.placement witness.before |>.symm
    center_adjacent_second :=
      localPlacementSideFace_adjacent_center (corridor := corridor)
        witness.placement witness.after
    first_adjacent_nextCenter :=
      localPlacementSideFace_adjacent_next_of_before_outgoing
        (corridor := corridor) hnext witness.placement witness.before
        witness.outgoing_after_before
    nextCenter_adjacent_second :=
      localPlacementSideFace_adjacent_next_of_after_outgoing
        (corridor := corridor) hnext witness.placement witness.after
        witness.after_after_outgoing |>.symm
    first_internal := localPlacementSideFace_internal (corridor := corridor)
      witness.placement witness.before
    second_internal := localPlacementSideFace_internal (corridor := corridor)
      witness.placement witness.after }
  · intro hfaces
    exact witness.before_ne_after
      (localPlacementSideFace_injective (corridor := corridor)
        witness.placement hfaces)
  · intro hfaces
    have hindices := skeleton.faceAt_injective hfaces
    have hvalues := congrArg Fin.val hindices
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega

/-- Two consecutive internal Cell-3 corridor faces construct their local
layer data directly.  The two rails are selected from the actual source face
slots immediately flanking the outgoing rung; no caller supplies exterior
faces or a synthetic transversal. -/
theorem exists_sourceLocalLayerPairWitness
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    Nonempty (SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) := by
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
  exact ⟨{
    placement := placement
    before := before
    after := after
    before_ne_after := hbeforeNeAfter
    outgoing_after_before := hbeforeActual
    after_after_outgoing := hafterActual }⟩

/-- Forgetting the source slots yields the existing local-layer interface.
This remains available for generic dual-cycle reasoning, while the canonical
source construction below retains the slots for exact cut calculations. -/
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
  rcases exists_sourceLocalLayerPairWitness corridor hunique leftInterior hnext with
    ⟨witness⟩
  exact ⟨witness.toLocalLayerPair⟩

/-- The canonical source witness keeps the real Cell-3 placement and flanking
slots available after the finite choice. -/
noncomputable def localLayerPairWitnessOfCorridor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (leftInterior : CorridorInterior blockLength)
    (hnext : leftInterior.center.val + 2 < blockLength) :
    SourceLocalLayerPairWitness web corridor hunique leftInterior hnext :=
  Classical.choice (exists_sourceLocalLayerPairWitness corridor hunique leftInterior hnext)

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
  (localLayerPairWitnessOfCorridor corridor hunique leftInterior hnext).toLocalLayerPair

/-- The first step of the source-local layer crosses the literal boundary
edge at the slot immediately before the outgoing rung. -/
theorem SourceLocalLayerPairWitness.firstWalk_crossingEdge_zero_eq_beforeEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      witness.toLocalLayerPair.firstWalk
      ⟨0, by simp [LocalLayerPair.firstWalk]⟩ =
      web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS witness.placement.root witness.before.1) := by
  let beforeDart := faceCycleDart web.annular.RS witness.placement.root
    witness.before.1
  have hbeforeInternal : dartOrbitFace web.annular.RS beforeDart ∈
      web.annular.cellulation.interiorFaces := by
    simpa [beforeDart] using
      localPlacementSideDart_internal (corridor := corridor)
        witness.placement witness.before
  have hcenterBoundary : web.annular.RS.edgeOf beforeDart ∈
      orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          leftInterior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS beforeDart
    rw [dartOrbitFace_faceCycleDart, witness.placement.root_face] at hraw
    exact hraw
  have hsideBoundary : web.annular.RS.edgeOf beforeDart ∈
      orbitFaceBoundary web.annular.RS
        (localPlacementSideFace witness.placement witness.before).1 := by
    change web.annular.RS.edgeOf beforeDart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS (web.annular.RS.alpha beforeDart))
    rw [← web.annular.RS.edge_alpha beforeDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha beforeDart)
  have hshared : web.annular.RS.edgeOf beforeDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (localPlacementSideFace witness.placement witness.before).1
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          leftInterior.center).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport web beforeDart hbeforeInternal,
      hsideBoundary, hcenterBoundary⟩
  change sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      (witness.toLocalLayerPair.firstWalk.adj_getVert_succ (by simp
        [LocalLayerPair.firstWalk])) = web.annular.RS.edgeOf beforeDart
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  simpa [SourceLocalLayerPairWitness.toLocalLayerPair,
    LocalLayerPair.firstWalk] using hshared

/-- The second step of the source-local layer crosses the literal boundary
edge at the slot immediately after the outgoing rung. -/
theorem SourceLocalLayerPairWitness.firstWalk_crossingEdge_one_eq_afterEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      witness.toLocalLayerPair.firstWalk
      ⟨1, by simp [LocalLayerPair.firstWalk]⟩ =
      web.annular.RS.edgeOf
        (faceCycleDart web.annular.RS witness.placement.root witness.after.1) := by
  let afterDart := faceCycleDart web.annular.RS witness.placement.root
    witness.after.1
  have hafterInternal : dartOrbitFace web.annular.RS afterDart ∈
      web.annular.cellulation.interiorFaces := by
    simpa [afterDart] using
      localPlacementSideDart_internal (corridor := corridor)
        witness.placement witness.after
  have hcenterBoundary : web.annular.RS.edgeOf afterDart ∈
      orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          leftInterior.center).1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      web.annular.RS afterDart
    rw [dartOrbitFace_faceCycleDart, witness.placement.root_face] at hraw
    exact hraw
  have hsideBoundary : web.annular.RS.edgeOf afterDart ∈
      orbitFaceBoundary web.annular.RS
        (localPlacementSideFace witness.placement witness.after).1 := by
    change web.annular.RS.edgeOf afterDart ∈
      orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS (web.annular.RS.alpha afterDart))
    rw [← web.annular.RS.edge_alpha afterDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha afterDart)
  have hshared : web.annular.RS.edgeOf afterDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          leftInterior.center).1
        (localPlacementSideFace witness.placement witness.after).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨InteriorFace.edge_mem_interiorEdgeSupport web afterDart hafterInternal,
      hcenterBoundary, hsideBoundary⟩
  change sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      (witness.toLocalLayerPair.firstWalk.adj_getVert_succ (by simp
        [LocalLayerPair.firstWalk])) = web.annular.RS.edgeOf afterDart
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  simpa [SourceLocalLayerPairWitness.toLocalLayerPair,
    LocalLayerPair.firstWalk] using hshared

/-- The first step through the next corridor hexagon crosses the third edge
at the corner before the outgoing rung. -/
theorem SourceLocalLayerPairWitness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      witness.toLocalLayerPair.secondWalk
      ⟨0, by simp [LocalLayerPair.secondWalk]⟩ =
      web.annular.RS.edgeOf
        (web.annular.RS.rho
          (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.before.1))) := by
  let beforeDart := faceCycleDart web.annular.RS witness.placement.root
    witness.before.1
  have hshared :=
    localPlacementThirdEdge_mem_sharedInteriorEdges_of_before_outgoing
      (corridor := corridor) hnext witness.placement witness.before
      witness.outgoing_after_before
  change sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      (witness.toLocalLayerPair.secondWalk.adj_getVert_succ (by simp
        [LocalLayerPair.secondWalk])) =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi beforeDart))
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  simpa [SourceLocalLayerPairWitness.toLocalLayerPair,
    LocalLayerPair.secondWalk, beforeDart] using hshared

/-- The second step through the next corridor hexagon crosses the other third
edge at the outgoing rung. -/
theorem SourceLocalLayerPairWitness.secondWalk_crossingEdge_one_eq_afterThirdEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      witness.toLocalLayerPair.secondWalk
      ⟨1, by simp [LocalLayerPair.secondWalk]⟩ =
      web.annular.RS.edgeOf
        (web.annular.RS.rho
          (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.placement.outgoingPosition))) := by
  let outgoingDart := faceCycleDart web.annular.RS witness.placement.root
    witness.placement.outgoingPosition
  have hshared :=
    localPlacementThirdEdge_mem_sharedInteriorEdges_of_after_outgoing
      (corridor := corridor) hnext witness.placement witness.after
      witness.after_after_outgoing
  change sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      (witness.toLocalLayerPair.secondWalk.adj_getVert_succ (by simp
        [LocalLayerPair.secondWalk])) =
      web.annular.RS.edgeOf
        (web.annular.RS.rho (web.annular.RS.phi outgoingDart))
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  simpa [SourceLocalLayerPairWitness.toLocalLayerPair,
    LocalLayerPair.secondWalk, outgoingDart] using hshared

/-- A two-step facial-dual walk has exactly the two explicitly identified
crossing edges.  This tiny finite reader is kept local to the source layer:
the facts passed to it are genuine edge equalities, not a cardinality claim. -/
private theorem dualWalkCrossingEdges_eq_pair_of_length_two
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hlength : walk.length = 2) (first second : G.edgeSet)
    (hzero : dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      hunique walk ⟨0, by omega⟩ = first)
    (hone : dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      hunique walk ⟨1, by omega⟩ = second) :
    dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      hunique walk = {first, second} := by
  ext edge
  rw [mem_dualWalkCrossingEdges_iff]
  constructor
  · rintro ⟨step, hstep⟩
    have hstepLt : step.val < 2 := by simpa [hlength] using step.isLt
    have hcases : step.val = 0 ∨ step.val = 1 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with hfirst | hsecond
    · have hcross : dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          walk step = first := by
        have hstepEq : step = (⟨0, by omega⟩ : Fin walk.length) := by
          apply Fin.ext
          exact hfirst
        simpa only [hstepEq] using hzero
      exact Or.inl (hstep.symm.trans hcross)
    · have hcross : dualWalkCrossingEdge (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          walk step = second := by
        have hstepEq : step = (⟨1, by omega⟩ : Fin walk.length) := by
          apply Fin.ext
          exact hsecond
        simpa only [hstepEq] using hone
      exact Or.inr (hstep.symm.trans hcross)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hmem
    rcases hmem with hfirst | hsecond
    · refine ⟨⟨0, by omega⟩, ?_⟩
      exact hzero.trans hfirst.symm
    · refine ⟨⟨1, by omega⟩, ?_⟩
      exact hone.trans hsecond.symm

/-- The literal Cell-3 dual loop cuts the four source edges read from its
two flanking slots and their two locally cubic corners.  This is the exact
finite wall, not merely a four-edge cardinality bound. -/
theorem SourceLocalLayerPairWitness.localLayerLoop_crossingEdges_eq_sourceCorners
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
      witness.toLocalLayerPair.localLayerLoop =
      {web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS witness.placement.root witness.before.1),
        web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS witness.placement.root witness.after.1)} ∪
      {web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.before.1))),
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.placement.outgoingPosition)))} := by
  have hfirstLength : witness.toLocalLayerPair.firstWalk.length = 2 := by
    simp [LocalLayerPair.firstWalk]
  have hsecondLength : witness.toLocalLayerPair.secondWalk.length = 2 := by
    simp [LocalLayerPair.secondWalk]
  have hfirst := dualWalkCrossingEdges_eq_pair_of_length_two
    witness.toLocalLayerPair.firstWalk hunique hfirstLength
    (web.annular.RS.edgeOf
      (faceCycleDart web.annular.RS witness.placement.root witness.before.1))
    (web.annular.RS.edgeOf
      (faceCycleDart web.annular.RS witness.placement.root witness.after.1))
    witness.firstWalk_crossingEdge_zero_eq_beforeEdge
    witness.firstWalk_crossingEdge_one_eq_afterEdge
  have hsecond := dualWalkCrossingEdges_eq_pair_of_length_two
    witness.toLocalLayerPair.secondWalk hunique hsecondLength
    (web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi
        (faceCycleDart web.annular.RS witness.placement.root
          witness.before.1))))
    (web.annular.RS.edgeOf
      (web.annular.RS.rho (web.annular.RS.phi
        (faceCycleDart web.annular.RS witness.placement.root
          witness.placement.outgoingPosition))))
    witness.secondWalk_crossingEdge_zero_eq_beforeThirdEdge
    witness.secondWalk_crossingEdge_one_eq_afterThirdEdge
  rw [LocalLayerPair.localLayerLoop, dualWalkCrossingEdges_append,
    dualWalkCrossingEdges_reverse, hfirst, hsecond]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
