import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRungPlacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInteriorFaceGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabSideAdjacency

/-!
# Choice-based local rung placements for Cell 3

The Cell-3 open tangle is not a closed cyclically-five-edge-connected graph,
so it must not inherit the global `PairwiseUniqueSharedInteriorEdges` premise
used to make corridor rungs canonical in the closed-minimal route.  A local
ladder needs less: one actual shared edge selected for each consecutive pair.
For an internal hexagon, the selected incoming and outgoing rungs are still
forced to occupy distinct positions by local face incidence alone.

This is the local rung part of Fable flag L1.  It neither classifies all
hexagon adjacencies nor constructs the eventual separated crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorInterfaceMatching
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

/-- A choice of one real primal shared edge for every consecutive facial-dual
corridor step.  This is deliberately weaker than pairwise uniqueness of all
face intersections. -/
structure SelectedCorridorRungs {E : Type*} [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength) where
  edge : CorridorStep corridorLength → E
  mem_left : ∀ step,
    edge step ∈ orbitFaceBoundary RS (corridor.faceAt step.left).1
  mem_right : ∀ step,
    edge step ∈ orbitFaceBoundary RS (corridor.faceAt step.right).1

namespace SelectedCorridorRungs

/-- Every incidence-level corridor has a choice-based rung selection. -/
noncomputable def choose {E : Type*} [Fintype E] [DecidableEq E]
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength) :
    SelectedCorridorRungs corridor where
  edge step := Classical.choose
    (corridor.exists_consecutive_rungEdge step.right_val)
  mem_left step :=
    (Classical.choose_spec
      (corridor.exists_consecutive_rungEdge step.right_val)).2.1
  mem_right step :=
    (Classical.choose_spec
      (corridor.exists_consecutive_rungEdge step.right_val)).2.2

end SelectedCorridorRungs

/-- The two selected corridor rungs, placed on the actual six-dart cycle of
one internal Cell-3 hexagon. -/
structure SelectedInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength) where
  root : web.annular.RS.D
  root_face : dartOrbitFace web.annular.RS root =
    (OrbitHexCorridorSkeleton.faceAt
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      interior.center).1
  orbit_card : (web.annular.RS.faceOrbit root).card = 6
  incomingPosition : Fin (web.annular.RS.faceOrbit root).card
  outgoingPosition : Fin (web.annular.RS.faceOrbit root).card
  incoming_edge : faceCycleEdge web.annular.RS root incomingPosition =
    rungs.edge interior.incoming
  outgoing_edge : faceCycleEdge web.annular.RS root outgoingPosition =
    rungs.edge interior.outgoing
  positions_ne : incomingPosition ≠ outgoingPosition

namespace SelectedInternalHexRungPlacement

def incomingPosition6
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) : Fin 6 :=
  Fin.cast placement.orbit_card placement.incomingPosition

def outgoingPosition6
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) : Fin 6 :=
  Fin.cast placement.orbit_card placement.outgoingPosition

theorem positions6_ne
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    placement.incomingPosition6 ≠ placement.outgoingPosition6 := by
  exact fun heq => placement.positions_ne
    (Fin.cast_injective placement.orbit_card heq)

def rungType
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    HexRungType :=
  hexRungType placement.incomingPosition6 placement.outgoingPosition6

theorem rungType_distance_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    placement.rungType.distance =
      hexCyclicDistance placement.incomingPosition6 placement.outgoingPosition6 :=
  hexRungType_distance_eq _ _ placement.positions6_ne

end SelectedInternalHexRungPlacement

/-- The four cyclic side positions remaining after the selected incoming and
outgoing rungs of one Cell-3 hexagon are removed.  This is only a local
coordinate interface; it does not yet construct rail walks or crosscuts. -/
def selectedPlacementSidePositions
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    Finset (Fin (web.annular.RS.faceOrbit placement.root).card) :=
  Finset.univ \ {placement.incomingPosition, placement.outgoingPosition}

@[simp]
theorem mem_selectedPlacementSidePositions_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : Fin (web.annular.RS.faceOrbit placement.root).card) :
    position ∈ selectedPlacementSidePositions placement ↔
      position ≠ placement.incomingPosition ∧ position ≠ placement.outgoingPosition := by
  simp [selectedPlacementSidePositions]

/-- A selected Cell-3 placement has exactly four non-rung side slots. -/
theorem card_selectedPlacementSidePositions_eq_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    (selectedPlacementSidePositions placement).card = 4 := by
  have hsubset :
      ({placement.incomingPosition, placement.outgoingPosition} :
        Finset (Fin (web.annular.RS.faceOrbit placement.root).card)) ⊆ Finset.univ := by
    simp
  rw [selectedPlacementSidePositions, Finset.card_sdiff_of_subset hsubset]
  simp [placement.positions_ne, placement.orbit_card]

/-- The literal face across one selected non-rung slot.  This definition uses
the opposite ambient dart directly; no global uniqueness of face intersections
is part of the data. -/
noncomputable def selectedPlacementSideFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)) :=
  ⟨dartOrbitFace web.annular.RS
      (web.annular.RS.alpha
        (faceCycleDart web.annular.RS placement.root position.1)),
    Finset.mem_univ _⟩

/-- The dart at every selected side slot remains on the certified interior
Cell-3 hexagon. -/
theorem selectedPlacementSideDart_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    dartOrbitFace web.annular.RS
        (faceCycleDart web.annular.RS placement.root position.1) ∈
      web.annular.cellulation.interiorFaces := by
  rw [dartOrbitFace_faceCycleDart, placement.root_face]
  exact corridor.face_internal interior.center

/-- The face across a selected side slot is not the corridor centre itself. -/
theorem selectedPlacementSideFace_val_ne_center
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    (selectedPlacementSideFace placement position).1 ≠
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center).1 := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  intro hsame
  change dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart) =
      ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
        interior.center).1 at hsame
  apply Instance.InteriorFace.dartOrbitFace_ne_alpha web sideDart
    (selectedPlacementSideDart_internal (corridor := corridor) placement position)
  calc
    dartOrbitFace web.annular.RS sideDart =
        dartOrbitFace web.annular.RS placement.root := by
          exact dartOrbitFace_faceCycleDart web.annular.RS placement.root position.1
    _ = ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1 := placement.root_face
    _ = dartOrbitFace web.annular.RS
        (web.annular.RS.alpha sideDart) := hsame.symm

/-- A selected side face is genuinely facial-dual adjacent to the Cell-3
corridor centre, witnessed by its own literal primal edge. -/
theorem selectedPlacementSideFace_adjacent_center
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center)
        (selectedPlacementSideFace placement position) := by
  let sideDart := faceCycleDart web.annular.RS placement.root position.1
  refine interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (orbitFace_incidence_le_two web.annular.RS)
    (e := web.annular.RS.edgeOf sideDart) ?_ ?_ ?_
  · intro hsame
    apply selectedPlacementSideFace_val_ne_center (corridor := corridor) placement position
    exact hsame.symm
  · change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
    have hside := edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS sideDart
    rw [dartOrbitFace_faceCycleDart, placement.root_face] at hside
    exact hside
  · change web.annular.RS.edgeOf sideDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha sideDart))
    rw [← web.annular.RS.edge_alpha sideDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha sideDart)

/-- Boundary cleanliness keeps every selected side face away from the two
annular holes. -/
theorem selectedPlacementSideFace_internal
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (position : {position // position ∈ selectedPlacementSidePositions placement}) :
    (selectedPlacementSideFace placement position).1 ∈
      web.annular.cellulation.interiorFaces := by
  exact corridor.neighbor_internal interior.center
    (selectedPlacementSideFace placement position)
    (selectedPlacementSideFace_adjacent_center (corridor := corridor) placement position)

/-- A collision between two distinct selected side slots has a concrete finite
local meaning: the centre hexagon and the repeated neighbouring face share two
different interior primal edges.  This is the residual case for the L1 local
classification; it is deliberately recorded rather than excluded by the
closed-map `PairwiseUniqueSharedInteriorEdges` premise. -/
theorem selectedPlacementSideFace_eq_implies_two_distinct_sharedInteriorEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {interior : CorridorInterior blockLength}
    (placement : SelectedInternalHexRungPlacement corridor rungs interior)
    (left right : {position // position ∈ selectedPlacementSidePositions placement})
    (hpositions : left.1 ≠ right.1)
    (hfaces : selectedPlacementSideFace placement left =
      selectedPlacementSideFace placement right) :
    ∃ first second,
      first ∈ sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
        (selectedPlacementSideFace placement left).1 ∧
      second ∈ sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton).faceAt
          interior.center).1
        (selectedPlacementSideFace placement left).1 ∧
      first ≠ second := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let leftDart := faceCycleDart web.annular.RS placement.root left.1
  let rightDart := faceCycleDart web.annular.RS placement.root right.1
  have hrootInternal : dartOrbitFace web.annular.RS placement.root ∈
      web.annular.cellulation.interiorFaces := by
    rw [placement.root_face]
    exact corridor.face_internal interior.center
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
        (selectedPlacementSideFace placement left).1 := by
    change web.annular.RS.edgeOf leftDart ∈ orbitFaceBoundary web.annular.RS
      (dartOrbitFace web.annular.RS (web.annular.RS.alpha leftDart))
    rw [← web.annular.RS.edge_alpha leftDart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart)
  have hfacesVal : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha leftDart) = dartOrbitFace web.annular.RS
        (web.annular.RS.alpha rightDart) := by
    exact congrArg Subtype.val hfaces
  have hrightAcross : web.annular.RS.edgeOf rightDart ∈
      orbitFaceBoundary web.annular.RS
        (selectedPlacementSideFace placement left).1 := by
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
        (selectedPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨Instance.InteriorFace.edge_mem_interiorEdgeSupport web leftDart
      (selectedPlacementSideDart_internal (corridor := corridor) placement left),
      hleftBoundary, hleftAcross⟩
  have hrightShared : web.annular.RS.edgeOf rightDart ∈
      sharedInteriorEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt interior.center).1
        (selectedPlacementSideFace placement left).1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).2
    exact ⟨Instance.InteriorFace.edge_mem_interiorEdgeSupport web rightDart
      (selectedPlacementSideDart_internal (corridor := corridor) placement right),
      hrightBoundary, hrightAcross⟩
  refine ⟨web.annular.RS.edgeOf leftDart, web.annular.RS.edgeOf rightDart,
    hleftShared, hrightShared, ?_⟩
  intro hedges
  apply hpositions
  apply Instance.InteriorFace.faceCycleEdge_injective web placement.root hrootInternal
  change web.annular.RS.edgeOf leftDart = web.annular.RS.edgeOf rightDart
  exact hedges

namespace Instance

/-- A boundary-clean Cell-3 corridor needs no global pairwise face-incidence
assumption to put one selected incoming and outgoing rung on every internal
hexagon. -/
theorem exists_selectedInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength) :
    Nonempty (SelectedInternalHexRungPlacement corridor rungs interior) := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  rcases exists_dartOrbitFace_eq web.annular.RS
      (skeleton.faceAt interior.center).1 with ⟨root, hroot⟩
  have hrootInternal : dartOrbitFace web.annular.RS root ∈
      web.annular.cellulation.interiorFaces := by
    rw [hroot]
    exact corridor.face_internal interior.center
  have horbitCard : (web.annular.RS.faceOrbit root).card = 6 := by
    calc
      (web.annular.RS.faceOrbit root).card =
          (orbitFaceDarts web.annular.RS
            (dartOrbitFace web.annular.RS root)).card := by
        rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      _ = (orbitFaceBoundary web.annular.RS
          (dartOrbitFace web.annular.RS root)).card := by
        exact (InteriorFace.boundary_card_eq_darts_card web root hrootInternal).symm
      _ = (orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.center).1).card := by rw [hroot]
      _ = 6 := skeleton.hexagonal interior.center
  have hincomingMem : rungs.edge interior.incoming ∈
      orbitFaceBoundary web.annular.RS (dartOrbitFace web.annular.RS root) := by
    rw [hroot]
    simpa using rungs.mem_right interior.incoming
  have houtgoingMem : rungs.edge interior.outgoing ∈
      orbitFaceBoundary web.annular.RS (dartOrbitFace web.annular.RS root) := by
    rw [hroot]
    exact rungs.mem_left interior.outgoing
  rcases InteriorFace.existsUnique_faceCycleEdge_eq web root hrootInternal
      (rungs.edge interior.incoming) hincomingMem with
    ⟨incomingPosition, hincomingEdge, _hincomingUnique⟩
  rcases InteriorFace.existsUnique_faceCycleEdge_eq web root hrootInternal
      (rungs.edge interior.outgoing) houtgoingMem with
    ⟨outgoingPosition, houtgoingEdge, _houtgoingUnique⟩
  have hpositionsNe : incomingPosition ≠ outgoingPosition := by
    intro hpositions
    have hrungs : rungs.edge interior.incoming = rungs.edge interior.outgoing := by
      rw [← hincomingEdge, ← houtgoingEdge, hpositions]
    have hpreviousCenter :
        (skeleton.faceAt interior.incoming.left).1 ≠
          (skeleton.faceAt interior.center).1 := by
      intro hfaces
      have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val - 1 = interior.center.val at hvalues
      have hpositive := interior.center_pos
      omega
    have hcenterNext :
        (skeleton.faceAt interior.center).1 ≠
          (skeleton.faceAt interior.outgoing.right).1 := by
      intro hfaces
      have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val = interior.center.val + 1 at hvalues
      omega
    have hpreviousNext :
        (skeleton.faceAt interior.incoming.left).1 ≠
          (skeleton.faceAt interior.outgoing.right).1 := by
      intro hfaces
      have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change interior.center.val - 1 = interior.center.val + 1 at hvalues
      have hpositive := interior.center_pos
      omega
    have hincomingPrevious : rungs.edge interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.incoming.left).1 :=
      rungs.mem_left interior.incoming
    have hincomingCenter : rungs.edge interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.center).1 := by
      simpa using rungs.mem_right interior.incoming
    have hnextOutgoing : rungs.edge interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.outgoing.right).1 := by
      rw [hrungs]
      exact rungs.mem_right interior.outgoing
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (orbitFace_incidence_le_two web.annular.RS)
        (skeleton.faceAt interior.center).2
        (skeleton.faceAt interior.incoming.left).2
        (skeleton.faceAt interior.outgoing.right).2
        hpreviousCenter.symm hincomingCenter hincomingPrevious hnextOutgoing
    rcases hcases with hcenterEqNext | hpreviousEqNext
    · exact hcenterNext hcenterEqNext.symm
    · exact hpreviousNext hpreviousEqNext.symm
  exact ⟨⟨root, hroot, horbitCard, incomingPosition, outgoingPosition,
    hincomingEdge, houtgoingEdge, hpositionsNe⟩⟩

/-- Canonically choose the locally available selected-rung placement. -/
noncomputable def selectedInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength) :
    SelectedInternalHexRungPlacement corridor rungs interior :=
  Classical.choice (exists_selectedInternalHexRungPlacement corridor rungs interior)

/-- The adjacent selected-rung case is impossible in a boundary-clean Cell-3
hexagon.  This uses local cubicity at the two exterior corners and the
geodesic separation of the three displayed corridor faces, not global
pairwise uniqueness of facial intersections. -/
theorem SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    placement.rungType ≠ HexRungType.adjacent := by
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  intro htype
  have hdistance : hexCyclicDistance placement.incomingPosition6
      placement.outgoingPosition6 = 1 := by
    rw [← placement.rungType_distance_eq, htype]
    rfl
  let incomingDart := faceCycleDart web.annular.RS placement.root
    placement.incomingPosition
  let outgoingDart := faceCycleDart web.annular.RS placement.root
    placement.outgoingPosition
  have hdartCases : outgoingDart = web.annular.RS.phi incomingDart ∨
      incomingDart = web.annular.RS.phi outgoingDart := by
    exact faceCycleDart_successor_or_reverse_of_hexCyclicDistance_eq_one
      web.annular.RS placement.root placement.orbit_card placement.incomingPosition
        placement.outgoingPosition hdistance
  have hincomingFace : dartOrbitFace web.annular.RS incomingDart =
      (skeleton.faceAt interior.center).1 := by
    calc
      dartOrbitFace web.annular.RS incomingDart =
          dartOrbitFace web.annular.RS placement.root := by
        exact dartOrbitFace_faceCycleDart web.annular.RS placement.root
          placement.incomingPosition
      _ = (skeleton.faceAt interior.center).1 := placement.root_face
  have houtgoingFace : dartOrbitFace web.annular.RS outgoingDart =
      (skeleton.faceAt interior.center).1 := by
    calc
      dartOrbitFace web.annular.RS outgoingDart =
          dartOrbitFace web.annular.RS placement.root := by
        exact dartOrbitFace_faceCycleDart web.annular.RS placement.root
          placement.outgoingPosition
      _ = (skeleton.faceAt interior.center).1 := placement.root_face
  have hincomingInternal : dartOrbitFace web.annular.RS incomingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [hincomingFace]
    exact corridor.face_internal interior.center
  have houtgoingInternal : dartOrbitFace web.annular.RS outgoingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal interior.center
  have hincomingEdge : web.annular.RS.edgeOf incomingDart =
      rungs.edge interior.incoming :=
    placement.incoming_edge
  have houtgoingEdge : web.annular.RS.edgeOf outgoingDart =
      rungs.edge interior.outgoing :=
    placement.outgoing_edge
  have hpreviousCenter :
      (skeleton.faceAt interior.incoming.left).1 ≠
        (skeleton.faceAt interior.center).1 := by
    intro hfaces
    have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val at hvalues
    have hpositive := interior.center_pos
    omega
  have hcenterNext :
      (skeleton.faceAt interior.center).1 ≠
        (skeleton.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val = interior.center.val + 1 at hvalues
    omega
  have hpreviousNext :
      (skeleton.faceAt interior.incoming.left).1 ≠
        (skeleton.faceAt interior.outgoing.right).1 := by
    intro hfaces
    have hindices := skeleton.faceAt_injective (Subtype.ext hfaces)
    have hvalues := congrArg Fin.val hindices
    change interior.center.val - 1 = interior.center.val + 1 at hvalues
    have hpositive := interior.center_pos
    omega
  have hincomingPrevious : web.annular.RS.edgeOf incomingDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt interior.incoming.left).1 := by
    rw [hincomingEdge]
    exact rungs.mem_left interior.incoming
  have houtgoingNext : web.annular.RS.edgeOf outgoingDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt interior.outgoing.right).1 := by
    rw [houtgoingEdge]
    exact rungs.mem_right interior.outgoing
  have hincomingOpposite : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha incomingDart) =
        (skeleton.faceAt interior.incoming.left).1 := by
    apply InteriorFace.alpha_face_eq_of_mem_other web incomingDart
      hincomingInternal (skeleton.faceAt interior.incoming.left).1
      hincomingPrevious
    rw [hincomingFace]
    exact hpreviousCenter.symm
  have houtgoingOpposite : dartOrbitFace web.annular.RS
      (web.annular.RS.alpha outgoingDart) =
        (skeleton.faceAt interior.outgoing.right).1 := by
    apply InteriorFace.alpha_face_eq_of_mem_other web outgoingDart
      houtgoingInternal (skeleton.faceAt interior.outgoing.right).1
      houtgoingNext
    rw [houtgoingFace]
    exact hcenterNext
  have hnotAdjacent := skeleton.separated_not_adjacent
    interior.incoming.left interior.outgoing.right (by
      change interior.center.val - 1 + 1 < interior.center.val + 1
      have hpositive := interior.center_pos
      omega)
  rcases hdartCases with hforward | hreverse
  · have hcornerNe : dartOrbitFace web.annular.RS
        (web.annular.RS.alpha incomingDart) ≠
          dartOrbitFace web.annular.RS
            (web.annular.RS.alpha (web.annular.RS.phi incomingDart)) := by
      rw [← hforward, hincomingOpposite, houtgoingOpposite]
      exact hpreviousNext
    have hcornerCard : (web.annular.RS.dartsAt
        (web.annular.RS.vertOf (web.annular.RS.alpha incomingDart))).card = 3 := by
      apply InteriorFace.dartsAt_card_eq_three web
      rw [hincomingOpposite]
      exact corridor.face_internal interior.incoming.left
    have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
      (InteriorFace.vertexRotationCyclic web) incomingDart hcornerCard hcornerNe
    apply hnotAdjacent
    convert hadj using 1 <;> apply Subtype.ext <;>
      simp only [hincomingOpposite, ← hforward, houtgoingOpposite]
  · have hcornerNe : dartOrbitFace web.annular.RS
        (web.annular.RS.alpha outgoingDart) ≠
          dartOrbitFace web.annular.RS
            (web.annular.RS.alpha (web.annular.RS.phi outgoingDart)) := by
      rw [← hreverse, houtgoingOpposite, hincomingOpposite]
      exact hpreviousNext.symm
    have hcornerCard : (web.annular.RS.dartsAt
        (web.annular.RS.vertOf (web.annular.RS.alpha outgoingDart))).card = 3 := by
      apply InteriorFace.dartsAt_card_eq_three web
      rw [houtgoingOpposite]
      exact corridor.face_internal interior.outgoing.right
    have hadj := oppositeFaces_adjacent_at_locally_cubic_corner web.annular.RS
      (InteriorFace.vertexRotationCyclic web) outgoingDart hcornerCard hcornerNe
    apply hnotAdjacent
    convert hadj.symm using 1 <;> apply Subtype.ext <;>
      simp only [houtgoingOpposite, ← hreverse, hincomingOpposite]

/-- The selected local Cell-3 rung is one of the two nonadjacent hexagon
types.  This is the finite branch point that remains for the literal ladder
classification. -/
theorem SelectedInternalHexRungPlacement.rungType_eq_oneEdgeBetween_or_opposite_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    placement.rungType = HexRungType.oneEdgeBetween ∨
      placement.rungType = HexRungType.opposite := by
  cases htype : placement.rungType with
  | adjacent =>
      exact (SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
        corridor rungs interior placement htype).elim
  | oneEdgeBetween => exact Or.inl rfl
  | opposite => exact Or.inr rfl

/-- The finite coordinate interface of a source-selected Cell-3 hexagon has
exactly two directed side steps.  This is the combinatorial input for a later
literal rail construction, not a proof that those steps assemble globally. -/
theorem selectedHexSideForwardSteps_card_eq_two_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength)
    (placement : SelectedInternalHexRungPlacement corridor rungs interior) :
    (hexSideForwardSteps placement.incomingPosition6 placement.outgoingPosition6).card = 2 := by
  apply card_hexSideForwardSteps_eq_two
  · exact placement.positions6_ne
  · intro hadjacent
    exact SelectedInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
      corridor rungs interior placement hadjacent

/-- Source-facing existence form: a boundary-clean Cell-3 corridor itself
supplies a choice of actual rungs and a nonadjacent two-rung placement at each
internal hexagon. -/
theorem exists_chosenSelectedInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (interior : CorridorInterior blockLength) :
    Nonempty (SelectedInternalHexRungPlacement corridor
      (SelectedCorridorRungs.choose
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
      interior) :=
  exists_selectedInternalHexRungPlacement corridor
    (SelectedCorridorRungs.choose
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    interior

/-- The source-facing selected-rung placement, with no global facial
intersection-uniqueness argument hidden in its construction. -/
noncomputable def chosenSelectedInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (interior : CorridorInterior blockLength) :
    SelectedInternalHexRungPlacement corridor
      (SelectedCorridorRungs.choose
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
      interior :=
  Classical.choice
    (exists_chosenSelectedInternalHexRungPlacement corridor interior)

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
