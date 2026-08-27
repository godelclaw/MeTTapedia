import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInteriorFaceGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorPointwiseRungs

/-!
# Source-local rung placements in a Cell-3 corridor

`InternalHexRungPlacement` is the finite six-cycle datum used by the corridor
calculus.  Its older existence theorem assumes global face two-sidedness,
which is unsuitable for a Cell-3 open tangle because its named hole stubs are
not two-sided.  A boundary-clean Cell-3 corridor uses only interior faces, so
the same placement can be constructed from their certified simple boundaries.
This is a local construction; it makes no claim about the two hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorPointwiseRungs
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24InducedHexCorridorTypes
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Formation

/-- Every internal hexagon of a boundary-clean corridor has its two literal
rungs at distinct positions of the real six-dart face cycle, from only the
pointwise consecutive-rung receipt.  In particular, this construction uses
neither a global colouring nor global pairwise face-intersection uniqueness. -/
theorem exists_localPointwiseInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength) :
    Nonempty (PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior) := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  rcases exists_dartOrbitFace_eq formation.annular.RS
      (skeleton.faceAt interior.center).1 with ⟨root, hroot⟩
  have hrootInternal : dartOrbitFace formation.annular.RS root ∈
      formation.annular.cellulation.interiorFaces := by
    rw [hroot]
    exact corridor.face_internal interior.center
  have horbitCard : (formation.annular.RS.faceOrbit root).card = 6 := by
    calc
      (formation.annular.RS.faceOrbit root).card =
          (orbitFaceDarts formation.annular.RS
            (dartOrbitFace formation.annular.RS root)).card := by
        rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      _ = (orbitFaceBoundary formation.annular.RS
          (dartOrbitFace formation.annular.RS root)).card := by
        exact (InteriorFace.boundary_card_eq_darts_card
          formation root hrootInternal).symm
      _ = (orbitFaceBoundary formation.annular.RS
          (skeleton.faceAt interior.center).1).card := by rw [hroot]
      _ = 6 := skeleton.hexagonal interior.center
  have hincomingMem : pointwiseRungEdge skeleton hlocal interior.incoming ∈
      orbitFaceBoundary formation.annular.RS
        (dartOrbitFace formation.annular.RS root) := by
    rw [hroot]
    simpa using pointwiseRungEdge_mem_right skeleton hlocal interior.incoming
  have houtgoingMem : pointwiseRungEdge skeleton hlocal interior.outgoing ∈
      orbitFaceBoundary formation.annular.RS
        (dartOrbitFace formation.annular.RS root) := by
    rw [hroot]
    exact pointwiseRungEdge_mem_left skeleton hlocal interior.outgoing
  rcases InteriorFace.existsUnique_faceCycleEdge_eq formation root hrootInternal
      (pointwiseRungEdge skeleton hlocal interior.incoming) hincomingMem with
    ⟨incomingPosition, hincomingEdge, _hincomingUnique⟩
  rcases InteriorFace.existsUnique_faceCycleEdge_eq formation root hrootInternal
      (pointwiseRungEdge skeleton hlocal interior.outgoing) houtgoingMem with
    ⟨outgoingPosition, houtgoingEdge, _houtgoingUnique⟩
  have hpositionsNe : incomingPosition ≠ outgoingPosition := by
    intro hpositions
    apply pointwiseRungEdge_incoming_ne_outgoing skeleton hlocal interior
    rw [← hincomingEdge, ← houtgoingEdge, hpositions]
  exact ⟨⟨root, hroot, horbitCard, incomingPosition, outgoingPosition,
    hincomingEdge, houtgoingEdge, hpositionsNe⟩⟩

/-- Canonical colouring-free placement selected from the local interface
receipt. -/
noncomputable def localPointwiseInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength) :
    PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior :=
  Classical.choice
    (exists_localPointwiseInternalHexRungPlacement formation corridor hlocal interior)

/-- The adjacent-rung case is impossible for a pointwise placement in an
internal Cell-3 hexagon.  All hypotheses are geometric fields of the
formation plus the consecutive-rung receipt. -/
theorem PointwiseInternalHexRungPlacement.rungType_ne_adjacent_of_cell3
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hlocal : ConsecutiveRungUnique
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton)
    (interior : CorridorInterior blockLength)
    (placement : PointwiseInternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hlocal interior) :
    placement.rungType ≠ HexRungType.adjacent := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  intro htype
  have hdistance : hexCyclicDistance placement.incomingPosition6
      placement.outgoingPosition6 = 1 := by
    rw [← placement.rungType_distance_eq, htype]
    rfl
  let incomingDart := faceCycleDart formation.annular.RS placement.root
    placement.incomingPosition
  let outgoingDart := faceCycleDart formation.annular.RS placement.root
    placement.outgoingPosition
  have hdartCases : outgoingDart = formation.annular.RS.phi incomingDart ∨
      incomingDart = formation.annular.RS.phi outgoingDart := by
    exact faceCycleDart_successor_or_reverse_of_hexCyclicDistance_eq_one
      formation.annular.RS placement.root placement.orbit_card
        placement.incomingPosition placement.outgoingPosition hdistance
  have hincomingFace : dartOrbitFace formation.annular.RS incomingDart =
      (skeleton.faceAt interior.center).1 := by
    calc
      dartOrbitFace formation.annular.RS incomingDart =
          dartOrbitFace formation.annular.RS placement.root := by
        exact dartOrbitFace_faceCycleDart formation.annular.RS placement.root
          placement.incomingPosition
      _ = (skeleton.faceAt interior.center).1 := placement.root_face
  have houtgoingFace : dartOrbitFace formation.annular.RS outgoingDart =
      (skeleton.faceAt interior.center).1 := by
    calc
      dartOrbitFace formation.annular.RS outgoingDart =
          dartOrbitFace formation.annular.RS placement.root := by
        exact dartOrbitFace_faceCycleDart formation.annular.RS placement.root
          placement.outgoingPosition
      _ = (skeleton.faceAt interior.center).1 := placement.root_face
  have hincomingInternal : dartOrbitFace formation.annular.RS incomingDart ∈
      formation.annular.cellulation.interiorFaces := by
    rw [hincomingFace]
    exact corridor.face_internal interior.center
  have houtgoingInternal : dartOrbitFace formation.annular.RS outgoingDart ∈
      formation.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal interior.center
  have hincomingEdge : formation.annular.RS.edgeOf incomingDart =
      pointwiseRungEdge skeleton hlocal interior.incoming :=
    placement.incoming_edge
  have houtgoingEdge : formation.annular.RS.edgeOf outgoingDart =
      pointwiseRungEdge skeleton hlocal interior.outgoing :=
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
  have hincomingPrevious : formation.annular.RS.edgeOf incomingDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt interior.incoming.left).1 := by
    rw [hincomingEdge]
    exact pointwiseRungEdge_mem_left skeleton hlocal interior.incoming
  have houtgoingNext : formation.annular.RS.edgeOf outgoingDart ∈
      orbitFaceBoundary formation.annular.RS
        (skeleton.faceAt interior.outgoing.right).1 := by
    rw [houtgoingEdge]
    exact pointwiseRungEdge_mem_right skeleton hlocal interior.outgoing
  have hincomingOpposite : dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha incomingDart) =
        (skeleton.faceAt interior.incoming.left).1 := by
    apply InteriorFace.alpha_face_eq_of_mem_other formation incomingDart
      hincomingInternal (skeleton.faceAt interior.incoming.left).1
      hincomingPrevious
    rw [hincomingFace]
    exact hpreviousCenter.symm
  have houtgoingOpposite : dartOrbitFace formation.annular.RS
      (formation.annular.RS.alpha outgoingDart) =
        (skeleton.faceAt interior.outgoing.right).1 := by
    apply InteriorFace.alpha_face_eq_of_mem_other formation outgoingDart
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
  · have hcornerNe : dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha incomingDart) ≠
          dartOrbitFace formation.annular.RS
            (formation.annular.RS.alpha
              (formation.annular.RS.phi incomingDart)) := by
      rw [← hforward, hincomingOpposite, houtgoingOpposite]
      exact hpreviousNext
    have hcornerCard : (formation.annular.RS.dartsAt
        (formation.annular.RS.vertOf
          (formation.annular.RS.alpha incomingDart))).card = 3 := by
      apply InteriorFace.dartsAt_card_eq_three formation
      rw [hincomingOpposite]
      exact corridor.face_internal interior.incoming.left
    have hadj := oppositeFaces_adjacent_at_locally_cubic_corner
      formation.annular.RS (InteriorFace.vertexRotationCyclic formation)
        incomingDart hcornerCard hcornerNe
    apply hnotAdjacent
    convert hadj using 1 <;> apply Subtype.ext <;>
      simp only [hincomingOpposite, ← hforward, houtgoingOpposite]
  · have hcornerNe : dartOrbitFace formation.annular.RS
        (formation.annular.RS.alpha outgoingDart) ≠
          dartOrbitFace formation.annular.RS
            (formation.annular.RS.alpha
              (formation.annular.RS.phi outgoingDart)) := by
      rw [← hreverse, houtgoingOpposite, hincomingOpposite]
      exact hpreviousNext.symm
    have hcornerCard : (formation.annular.RS.dartsAt
        (formation.annular.RS.vertOf
          (formation.annular.RS.alpha outgoingDart))).card = 3 := by
      apply InteriorFace.dartsAt_card_eq_three formation
      rw [houtgoingOpposite]
      exact corridor.face_internal interior.outgoing.right
    have hadj := oppositeFaces_adjacent_at_locally_cubic_corner
      formation.annular.RS (InteriorFace.vertexRotationCyclic formation)
        outgoingDart hcornerCard hcornerNe
    apply hnotAdjacent
    convert hadj.symm using 1 <;> apply Subtype.ext <;>
      simp only [houtgoingOpposite, ← hreverse, hincomingOpposite]

end Formation

namespace Instance

/-- Every internal hexagon of a boundary-clean Cell-3 corridor has its two
actual corridor rungs at distinct positions of its real six-dart facial
cycle.  The distinctness proof uses only the three locally different corridor
faces and the universal at-most-two face incidence bound. -/
theorem exists_localInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (interior : CorridorInterior blockLength) :
    Nonempty (InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior) := by
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
  have hincomingMem : skeleton.rungEdge hunique interior.incoming ∈
      orbitFaceBoundary web.annular.RS (dartOrbitFace web.annular.RS root) := by
    rw [hroot]
    simpa using skeleton.rungEdge_mem_right hunique interior.incoming
  have houtgoingMem : skeleton.rungEdge hunique interior.outgoing ∈
      orbitFaceBoundary web.annular.RS (dartOrbitFace web.annular.RS root) := by
    rw [hroot]
    exact skeleton.rungEdge_mem_left hunique interior.outgoing
  rcases InteriorFace.existsUnique_faceCycleEdge_eq web root hrootInternal
      (skeleton.rungEdge hunique interior.incoming) hincomingMem with
    ⟨incomingPosition, hincomingEdge, _hincomingUnique⟩
  rcases InteriorFace.existsUnique_faceCycleEdge_eq web root hrootInternal
      (skeleton.rungEdge hunique interior.outgoing) houtgoingMem with
    ⟨outgoingPosition, houtgoingEdge, _houtgoingUnique⟩
  have hpositionsNe : incomingPosition ≠ outgoingPosition := by
    intro hpositions
    have hrungs : skeleton.rungEdge hunique interior.incoming =
        skeleton.rungEdge hunique interior.outgoing := by
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
    have hincomingPrevious : skeleton.rungEdge hunique interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.incoming.left).1 :=
      skeleton.rungEdge_mem_left hunique interior.incoming
    have hincomingCenter : skeleton.rungEdge hunique interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.center).1 := by
      simpa using skeleton.rungEdge_mem_right hunique interior.incoming
    have hnextOutgoing : skeleton.rungEdge hunique interior.incoming ∈
        orbitFaceBoundary web.annular.RS
          (skeleton.faceAt interior.outgoing.right).1 := by
      rw [hrungs]
      exact skeleton.rungEdge_mem_right hunique interior.outgoing
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

/-- Canonical local choice of the real Cell-3 rung placement. -/
noncomputable def localInternalHexRungPlacement
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (interior : CorridorInterior blockLength) :
    InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior :=
  Classical.choice (exists_localInternalHexRungPlacement corridor hunique interior)

/-- The adjacent-rung case is impossible for an internally placed Cell-3
hexagon.  This is the ordinary induced-corridor argument, but its two corner
uses of cubicity are discharged from the corresponding interior faces rather
than from an invalid global cubicity hypothesis. -/
theorem InternalHexRungPlacement.rungType_ne_adjacent_of_cell3
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (interior : CorridorInterior blockLength)
    (placement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique interior) :
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
      skeleton.rungEdge hunique interior.incoming :=
    placement.incoming_edge
  have houtgoingEdge : web.annular.RS.edgeOf outgoingDart =
      skeleton.rungEdge hunique interior.outgoing :=
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
    exact skeleton.rungEdge_mem_left hunique interior.incoming
  have houtgoingNext : web.annular.RS.edgeOf outgoingDart ∈
      orbitFaceBoundary web.annular.RS
        (skeleton.faceAt interior.outgoing.right).1 := by
    rw [houtgoingEdge]
    exact skeleton.rungEdge_mem_right hunique interior.outgoing
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

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
