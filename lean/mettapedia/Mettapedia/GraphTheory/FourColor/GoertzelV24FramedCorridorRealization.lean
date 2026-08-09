import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCorridorInterfaceMatching
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrientedHexSlab

/-!
# Source-realized clean corridor axes

The compositional route does not begin a splice from an arbitrary graph-side
cut.  Its L1 formation first supplies a long, clean interval of the annular
facial dual.  This file makes that interval a concrete Lean object: the
selected block remains a literal subwalk of the geodesic delivered by framed
L1, and every face and neighbouring full-dual face on it is certified
hexagonal.

This is deliberately a formation object rather than another splice premise.
The next layer can construct its two transverse open interfaces from this
actual corridor axis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual clean block selected from the framed L1 geodesic.  Unlike the
older existential conclusion, this retains the path, its chosen block, and
the literal source position of every corridor face. -/
structure BoundaryCleanCorridorRealization {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) where
  initialFace : AmbientFace embedded.cellulation.interiorFaces
  terminalFace : AmbientFace embedded.cellulation.interiorFaces
  path : (interiorDualGraph
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    embedded.cellulation.interiorFaces).Walk initialFace terminalFace
  isPath : path.IsPath
  geodesic : path.length =
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).dist initialFace terminalFace
  positionCount :
    (embedded.boundaryCleanContaminationBudget + 1) * blockLength ≤
      path.length + 1
  block : Fin (embedded.boundaryCleanContaminationBudget + 1)
  clean : ∀ offset : Fin blockLength,
    let position := corridorBlockIndex
      (defectBudget := embedded.boundaryCleanContaminationBudget)
      block offset
    let selected := path.getVert position.val
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      selected.1).card = 6 ∧
      ∀ neighbor : AmbientFace (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)),
        (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
            (embedded.internalFaceToFull selected) neighbor →
          neighbor.1 ∈ embedded.cellulation.interiorFaces ∧
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
              neighbor.1).card = 6

/-- Forgetting the retained witness recovers the existing framed L1
proposition exactly. -/
theorem BoundaryCleanCorridorRealization.to_hasBoundaryCleanBlock
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) :
    embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength := by
  exact ⟨realization.initialFace, realization.terminalFace, realization.path,
    realization.isPath, realization.geodesic, realization.positionCount,
    realization.block, realization.clean⟩

/-- Package an existing framed L1 conclusion without losing its constructive
geodesic and selected clean block. -/
theorem BoundaryCleanCorridorRealization.exists_of_hasBoundaryCleanBlock
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (hclean : embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    Nonempty (BoundaryCleanCorridorRealization embedded blockLength) := by
  rcases hclean with
    ⟨start, finish, path, isPath, geodesic, positionCount, block, clean⟩
  exact ⟨⟨start, finish, path, isPath, geodesic, positionCount, block, clean⟩⟩

/-- The source position at which the selected block starts. -/
def BoundaryCleanCorridorRealization.coreStart
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) : Nat :=
  realization.block.val * blockLength

/-- The literal interval of the original L1 geodesic selected as the clean
corridor axis.  It is not a re-created path or a caller-supplied boundary. -/
def BoundaryCleanCorridorRealization.coreWalk
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) :=
  (realization.path.drop realization.coreStart).take (blockLength - 1)

theorem BoundaryCleanCorridorRealization.coreStart_add_length_sub_one_le
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) :
    realization.coreStart + (blockLength - 1) ≤ realization.path.length := by
  have hblock : realization.block.val + 1 ≤
      embedded.boundaryCleanContaminationBudget + 1 := by
    omega
  have hscaled : (realization.block.val + 1) * blockLength ≤
      (embedded.boundaryCleanContaminationBudget + 1) * blockLength :=
    Nat.mul_le_mul_right blockLength hblock
  have hroom : (realization.block.val + 1) * blockLength ≤
      realization.path.length + 1 := hscaled.trans realization.positionCount
  have hroom' : realization.block.val * blockLength + blockLength ≤
      realization.path.length + 1 := by
    simpa [Nat.add_mul] using hroom
  change realization.block.val * blockLength + (blockLength - 1) ≤
    realization.path.length
  omega

/-- The selected corridor has exactly the requested number of facial-dual
positions. -/
theorem BoundaryCleanCorridorRealization.coreWalk_length
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) :
    realization.coreWalk.length = blockLength - 1 := by
  have hle : blockLength - 1 ≤ realization.path.length - realization.coreStart :=
    Nat.le_sub_of_add_le
      (by
        simpa [Nat.add_comm] using
          realization.coreStart_add_length_sub_one_le hpositive)
  simp [BoundaryCleanCorridorRealization.coreWalk, Nat.min_eq_left hle]

/-- Taking an interval of the source geodesic preserves simplicity. -/
theorem BoundaryCleanCorridorRealization.coreWalk_isPath
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) :
    realization.coreWalk.IsPath := by
  exact (realization.isPath.drop realization.coreStart).take _

/-- Every position of the realized corridor axis is definitionally the
corresponding selected position of the original framed L1 path. -/
theorem BoundaryCleanCorridorRealization.coreWalk_getVert
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) (offset : Fin blockLength) :
    realization.coreWalk.getVert offset.val =
      realization.path.getVert
        (corridorBlockIndex
          (defectBudget := embedded.boundaryCleanContaminationBudget)
          realization.block offset).val := by
  have hle : offset.val ≤ blockLength - 1 := by omega
  simp [BoundaryCleanCorridorRealization.coreWalk,
    BoundaryCleanCorridorRealization.coreStart, corridorBlockIndex,
    Nat.min_eq_right hle]

/-- The selected axis consists of genuine hexagonal faces in the embedded
source cellulation. -/
theorem BoundaryCleanCorridorRealization.coreWalk_hexagonal
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) (offset : Fin blockLength) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      (realization.coreWalk.getVert offset.val).1).card = 6 := by
  rw [realization.coreWalk_getVert hpositive offset]
  exact (realization.clean offset).1

/-- Every full-dual neighbour of a selected corridor face is also hexagonal.
This is the local source condition from which the two slab-side tracks will
be constructed, rather than an abstract assumption on a splice boundary. -/
theorem BoundaryCleanCorridorRealization.coreWalk_neighbor_hexagonal
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) (offset : Fin blockLength)
    (neighbor : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hadj : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      (embedded.internalFaceToFull (realization.coreWalk.getVert offset.val))
      neighbor) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      neighbor.1).card = 6 := by
  rw [realization.coreWalk_getVert hpositive offset] at hadj
  exact ((realization.clean offset).2 neighbor hadj).2

/-- Every full-dual neighbor of a selected corridor face remains an internal
annular face.  This preserves the boundary-clean construction's explicit
avoidance of both container holes for the later rail and separator steps. -/
theorem BoundaryCleanCorridorRealization.coreWalk_neighbor_internal
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hpositive : 0 < blockLength) (offset : Fin blockLength)
    (neighbor : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hadj : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
      (embedded.internalFaceToFull (realization.coreWalk.getVert offset.val))
      neighbor) :
    neighbor.1 ∈ embedded.cellulation.interiorFaces := by
  rw [realization.coreWalk_getVert hpositive offset] at hadj
  exact ((realization.clean offset).2 neighbor hadj).1

/-- The finite-interface corridor is constructed directly from the retained
source geodesic.  In particular, its faces are not an arbitrary clean
corridor supplied later by a caller. -/
noncomputable def BoundaryCleanCorridorRealization.toCleanOrbitHexCorridorSkeleton
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) :
    CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let boundary := orbitFaceBoundary RS
  let internalFaces := embedded.cellulation.interiorFaces
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let internalDual := interiorDualGraph boundary internalFaces
  let fullDual := interiorDualGraph boundary allFaces
  let badBudget := embedded.boundaryCleanContaminationBudget
  have hpositionCount : (badBudget + 1) * blockLength ≤
      realization.path.length + 1 := by
    simpa [badBudget] using realization.positionCount
  have hadj_iff (left right : AmbientFace internalFaces) :
      internalDual.Adj left right ↔
        fullDual.Adj (embedded.internalFaceToFull left)
          (embedded.internalFaceToFull right) := by
    constructor
    · intro hinternal
      rcases (interiorDualGraph_adj_iff boundary internalFaces).1 hinternal with
          ⟨hne, edge, _hinterior, hleft, hright⟩
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          boundary allFaces (orbitFace_incidence_le_two RS)
            hne hleft hright
    · intro hfull
      rcases (interiorDualGraph_adj_iff boundary allFaces).1 hfull with
          ⟨hne, edge, _hinterior, hleft, hright⟩
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          boundary internalFaces embedded.internalFace_incidence_le_two
            hne hleft hright
  let corridor : OrbitHexCorridorSkeleton RS blockLength := {
    faceAt := fun offset =>
      embedded.internalFaceToFull
        (realization.path.getVert
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block offset).val)
    faceAt_injective := by
      intro left right hfaces
      have hvertices :
          realization.path.getVert
              (corridorBlockIndex (defectBudget := badBudget)
                realization.block left).val =
            realization.path.getVert
              (corridorBlockIndex (defectBudget := badBudget)
                realization.block right).val :=
        embedded.internalFaceToFull_injective hfaces
      have hleftBound :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block left).val ≤ realization.path.length := by
        have hindex := (corridorBlockIndex (defectBudget := badBudget)
          realization.block left).isLt
        omega
      have hrightBound :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block right).val ≤ realization.path.length := by
        have hindex := (corridorBlockIndex (defectBudget := badBudget)
          realization.block right).isLt
        omega
      have hindices := realization.isPath.getVert_injOn
        (by simpa using hleftBound) (by simpa using hrightBound) hvertices
      apply Fin.ext
      change realization.block.val * blockLength + left.val =
        realization.block.val * blockLength + right.val at hindices
      omega
    hexagonal := by
      intro offset
      exact (realization.clean offset).1
    consecutive_adjacent := by
      intro left right hsuccessor
      have hrightBound :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block right).val ≤ realization.path.length := by
        have hindex := (corridorBlockIndex (defectBudget := badBudget)
          realization.block right).isLt
        omega
      have hleftStrict :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block left).val < realization.path.length := by
        change realization.block.val * blockLength + left.val <
          realization.path.length
        change realization.block.val * blockLength + right.val ≤
          realization.path.length at hrightBound
        omega
      apply (hadj_iff _ _).1
      have hadj := realization.path.adj_getVert_succ hleftStrict
      change internalDual.Adj
        (realization.path.getVert
          (realization.block.val * blockLength + left.val))
        (realization.path.getVert
          (realization.block.val * blockLength + right.val))
      change internalDual.Adj
        (realization.path.getVert
          (realization.block.val * blockLength + left.val))
        (realization.path.getVert
          ((realization.block.val * blockLength + left.val) + 1)) at hadj
      simpa only [hsuccessor, Nat.add_assoc] using hadj
    separated_not_adjacent := by
      intro left right hseparated hfull
      have hleftBound :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block left).val ≤ realization.path.length := by
        have hindex := (corridorBlockIndex (defectBudget := badBudget)
          realization.block left).isLt
        omega
      have hrightBound :
          (corridorBlockIndex (defectBudget := badBudget)
            realization.block right).val ≤ realization.path.length := by
        have hindex := (corridorBlockIndex (defectBudget := badBudget)
          realization.block right).isLt
        omega
      apply (not_adj_getVert_of_length_eq_dist_of_add_one_lt
        realization.path realization.geodesic
        (corridorBlockIndex (defectBudget := badBudget)
          realization.block left).val
        (corridorBlockIndex (defectBudget := badBudget)
          realization.block right).val
        hleftBound hrightBound (by
          change realization.block.val * blockLength + left.val + 1 <
            realization.block.val * blockLength + right.val
          omega))
      exact (hadj_iff _ _).2 hfull
  }
  exact {
    toOrbitHexCorridorSkeleton := corridor
    neighbor_hexagonal := by
      intro offset neighbor hadj
      exact ((realization.clean offset).2 neighbor hadj).2
  }

/-- The face selected by the concrete clean-corridor carrier is exactly the
face at the corresponding source block position. -/
theorem BoundaryCleanCorridorRealization.toCleanOrbitHexCorridorSkeleton_faceAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (offset : Fin blockLength) :
    (realization.toCleanOrbitHexCorridorSkeleton
      |>.toOrbitHexCorridorSkeleton.faceAt offset) =
      embedded.internalFaceToFull
        (realization.path.getVert
        (corridorBlockIndex
            (defectBudget := embedded.boundaryCleanContaminationBudget)
            realization.block offset).val) := by
  rfl

/-- A full-dual face cannot meet two source-corridor positions more than two
steps apart.  Boundary cleanliness first returns that face to the internal
annular dual; the retained L1 geodesic then excludes the resulting two-step
shortcut.  Thus any later collision of the two rail tracks is confined to a
bounded local window. -/
theorem BoundaryCleanCorridorRealization.no_common_fullNeighbor_of_add_two_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (left right : Fin blockLength) (hseparated : left.val + 2 < right.val) :
    ¬ ∃ neighbor : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)),
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt left) neighbor ∧
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
        (realization.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton.faceAt right) neighbor := by
  rintro ⟨neighbor, hleft, hright⟩
  rw [realization.toCleanOrbitHexCorridorSkeleton_faceAt] at hleft hright
  let boundary := orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
  let internalFaces := embedded.cellulation.interiorFaces
  let allFaces : Finset (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
    Finset.univ
  let internalDual := interiorDualGraph boundary internalFaces
  let leftIndex := corridorBlockIndex
    (defectBudget := embedded.boundaryCleanContaminationBudget)
    realization.block left
  let rightIndex := corridorBlockIndex
    (defectBudget := embedded.boundaryCleanContaminationBudget)
    realization.block right
  have hneighborInternal : neighbor.1 ∈ internalFaces := by
    exact ((realization.clean left).2 neighbor hleft).1
  let internalNeighbor : AmbientFace internalFaces :=
    ⟨neighbor.1, hneighborInternal⟩
  have hleftInternal : internalDual.Adj
      (realization.path.getVert leftIndex.val) internalNeighbor := by
    rcases (interiorDualGraph_adj_iff boundary allFaces).1 hleft with
      ⟨hne, edge, _hinterior, hleftEdge, hneighborEdge⟩
    exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      boundary internalFaces embedded.internalFace_incidence_le_two
      hne hleftEdge (by simpa [internalNeighbor] using hneighborEdge)
  have hrightInternal : internalDual.Adj
      (realization.path.getVert rightIndex.val) internalNeighbor := by
    rcases (interiorDualGraph_adj_iff boundary allFaces).1 hright with
      ⟨hne, edge, _hinterior, hrightEdge, hneighborEdge⟩
    exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      boundary internalFaces embedded.internalFace_incidence_le_two
      hne hrightEdge (by simpa [internalNeighbor] using hneighborEdge)
  have hleftBound : leftIndex.val ≤ realization.path.length := by
    have hindex := leftIndex.isLt
    have hpositionCount := realization.positionCount
    dsimp [leftIndex, corridorBlockIndex] at hindex ⊢
    omega
  have hrightBound : rightIndex.val ≤ realization.path.length := by
    have hindex := rightIndex.isLt
    have hpositionCount := realization.positionCount
    dsimp [rightIndex, corridorBlockIndex] at hindex ⊢
    omega
  apply not_exists_common_neighbor_getVert_of_length_eq_dist_of_add_two_lt
    realization.path realization.geodesic leftIndex.val rightIndex.val
    hleftBound hrightBound
  · change realization.block.val * blockLength + left.val + 2 <
      realization.block.val * blockLength + right.val
    omega
  · exact ⟨internalNeighbor, hleftInternal, hrightInternal.symm⟩

/-- Side faces selected from source-corridor positions separated by more than
two steps are distinct.  A common side face would be a full-dual neighbor of
both axis faces, which the retained L1 geodesic excludes.  This reduces the
remaining rail-intersection analysis to a bounded local window. -/
theorem BoundaryCleanCorridorRealization.placementSideNeighbor_ne_of_add_two_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    {left right : CorridorInterior blockLength}
    (leftPlacement : InternalHexRungPlacement
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique left)
    (rightPlacement : InternalHexRungPlacement
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique right)
    (leftPosition : {position // position ∈ placementSidePositions leftPlacement})
    (rightPosition : {position // position ∈ placementSidePositions rightPlacement})
    (hseparated : left.center.val + 2 < right.center.val) :
    placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
      hunique leftPlacement leftPosition ≠
      placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton htwoSided
        hunique rightPlacement rightPosition := by
  intro hsame
  apply realization.no_common_fullNeighbor_of_add_two_lt
    left.center right.center hseparated
  refine ⟨placementSideNeighbor realization.toCleanOrbitHexCorridorSkeleton
    htwoSided hunique leftPlacement leftPosition, ?_, ?_⟩
  · exact internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique left (placementSideEdge htwoSided leftPlacement leftPosition)
  · rw [hsame]
    exact internalSideNeighbor_adjacent realization.toCleanOrbitHexCorridorSkeleton
      htwoSided hunique right (placementSideEdge htwoSided rightPlacement rightPosition)

/-- Two walks whose faces are each anchored at a pair of consecutive source
corridor cells have disjoint supports once the pairs are separated by a
three-cell gap.  Any shared face would be a full-dual neighbor of two axis
positions more than two steps apart, contradicting the retained L1 geodesic.
This is the nonlocal part of rail simplicity; only a bounded local window
remains for the source-cell case analysis. -/
theorem BoundaryCleanCorridorRealization.walkSupports_disjoint_of_two_source_anchor_pairs_of_add_three_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    {leftInterior rightInterior : CorridorInterior blockLength}
    (hleftNext : leftInterior.center.val + 2 < blockLength)
    (hrightNext : rightInterior.center.val + 2 < blockLength)
    {leftStart leftFinish rightStart rightFinish : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
    (leftWalk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      leftStart leftFinish)
    (rightWalk : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      rightStart rightFinish)
    (hleft : ∀ face ∈ leftWalk.support,
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (realization.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt leftInterior.center) face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (realization.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior leftInterior hleftNext).center) face)
    (hright : ∀ face ∈ rightWalk.support,
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (realization.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt rightInterior.center) face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (realization.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt
              (nextCorridorInterior rightInterior hrightNext).center) face)
    (hseparated : leftInterior.center.val + 3 < rightInterior.center.val) :
    leftWalk.support.Disjoint rightWalk.support := by
  rw [List.disjoint_left]
  intro face hleftFace hrightFace
  rcases hleft face hleftFace with hleftStart | hleftNextFace
  · rcases hright face hrightFace with hrightStart | hrightNextFace
    · exact realization.no_common_fullNeighbor_of_add_two_lt
        leftInterior.center rightInterior.center (by omega)
        ⟨face, hleftStart, hrightStart⟩
    · exact realization.no_common_fullNeighbor_of_add_two_lt
        leftInterior.center (nextCorridorInterior rightInterior hrightNext).center
        (by
          change leftInterior.center.val + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleftStart, hrightNextFace⟩
  · rcases hright face hrightFace with hrightStart | hrightNextFace
    · exact realization.no_common_fullNeighbor_of_add_two_lt
        (nextCorridorInterior leftInterior hleftNext).center rightInterior.center
        (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val
          omega)
        ⟨face, hleftNextFace, hrightStart⟩
    · exact realization.no_common_fullNeighbor_of_add_two_lt
        (nextCorridorInterior leftInterior hleftNext).center
        (nextCorridorInterior rightInterior hrightNext).center
        (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleftNextFace, hrightNextFace⟩

/-- Framed weighted L1 supplies a source-realized clean corridor, including
the actual geodesic and block that the subsequent interface construction must
use. -/
theorem exists_boundaryCleanCorridorRealization_of_weightedL9
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.boundaryCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    Nonempty (BoundaryCleanCorridorRealization embedded blockLength) := by
  apply BoundaryCleanCorridorRealization.exists_of_hasBoundaryCleanBlock
  exact embedded.exists_boundaryCleanHexagonalGeodesicBlock_of_weightedL9
    hsource geometry blockLength hpositive hlarge

/-- The previous finite-interface transfer carrier is now available from the
same source-realized corridor; this adapter does not introduce a new route or
an assumed transverse boundary. -/
theorem BoundaryCleanCorridorRealization.nonempty_cleanOrbitHexCorridorSkeleton
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength) :=
  embedded.nonempty_cleanOrbitHexCorridorSkeleton_of_boundaryCleanBlock
    blockLength realization.to_hasBoundaryCleanBlock

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
