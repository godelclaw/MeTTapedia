import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedInteriorDual
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedWeightedCorridor

/-!
# Boundary-clean corridors inside embedded source trails

The internal annular dual omits the two container-hole faces.  A block clean
only in that induced dual may nevertheless touch a hole, so it is not yet the
translation-invariant full-face slab consumed by the corridor transfer
engine.  This module keeps those boundary contacts visible and charges them
to the actual hole perimeter already present in framed L9.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexPathExtraction
open GoertzelV24HexCorridorSkeleton
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- An internal annular face included into the full quotient-face carrier. -/
def internalFaceToFull {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  ⟨face.1, Finset.mem_univ _⟩

theorem internalFaceToFull_injective {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Function.Injective embedded.internalFaceToFull := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun face => face.1) heq

/-- Full-dual faces adjacent to at least one of the two named holes. -/
def holeAdjacentFullFaces {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Finset (AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))) := by
  classical
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  let fullDual := interiorDualGraph boundary
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))
  exact embedded.cellulation.holeFaces.biUnion fun hole =>
    fullDual.neighborFinset ⟨hole, Finset.mem_univ _⟩

/-- Internal faces adjacent in the full facial dual to a container hole. -/
def holeAdjacentInteriorFaces {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Finset (AmbientFace embedded.cellulation.interiorFaces) :=
  Finset.univ.filter fun face =>
    embedded.internalFaceToFull face ∈ embedded.holeAdjacentFullFaces

@[simp]
theorem mem_holeAdjacentInteriorFaces_iff {source : SourceTrail G}
    (embedded : source.AnnularEmbedding)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    face ∈ embedded.holeAdjacentInteriorFaces ↔
      embedded.internalFaceToFull face ∈ embedded.holeAdjacentFullFaces := by
  simp [holeAdjacentInteriorFaces]

/-- The full-dual neighborhood of the two holes is no larger than their
total dart perimeter.  Repeated boundary edges only make this estimate
looser, never unsound. -/
theorem card_holeAdjacentFullFaces_le_holePerimeter
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    embedded.holeAdjacentFullFaces.card ≤
      embedded.cellulation.holePerimeter := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let boundary := orbitFaceBoundary RS
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let fullDual := interiorDualGraph boundary allFaces
  letI : DecidableRel fullDual.Adj := Classical.decRel _
  calc
    embedded.holeAdjacentFullFaces.card ≤
        ∑ hole ∈ embedded.cellulation.holeFaces,
          (fullDual.neighborFinset
            (⟨hole, Finset.mem_univ _⟩ : AmbientFace allFaces)).card := by
      simpa [holeAdjacentFullFaces, RS, boundary, allFaces, fullDual] using
        (Finset.card_biUnion_le :
          (embedded.cellulation.holeFaces.biUnion fun hole =>
            fullDual.neighborFinset
              (⟨hole, Finset.mem_univ _⟩ : AmbientFace allFaces)).card ≤
          ∑ hole ∈ embedded.cellulation.holeFaces,
            (fullDual.neighborFinset
              (⟨hole, Finset.mem_univ _⟩ : AmbientFace allFaces)).card)
    _ ≤ ∑ hole ∈ embedded.cellulation.holeFaces,
          (boundary hole).card := by
      apply Finset.sum_le_sum
      intro hole hhole
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact interiorDualGraph_degree_le_faceBoundary_card
        boundary allFaces (orbitFace_incidence_le_two RS)
          ⟨hole, Finset.mem_univ _⟩
    _ ≤ ∑ hole ∈ embedded.cellulation.holeFaces,
          (orbitFaceDarts RS hole).card := by
      apply Finset.sum_le_sum
      intro hole hhole
      exact orbitFaceBoundary_card_le_orbitFaceDarts_card RS hole
    _ = embedded.cellulation.holePerimeter := by
      simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holePerimeter,
        GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength,
        RS]

theorem card_holeAdjacentInteriorFaces_le_holePerimeter
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    embedded.holeAdjacentInteriorFaces.card ≤
      embedded.cellulation.holePerimeter := by
  let inclusion : {face // face ∈ embedded.holeAdjacentInteriorFaces} →
      {face // face ∈ embedded.holeAdjacentFullFaces} := fun face =>
    ⟨embedded.internalFaceToFull face.1,
      (embedded.mem_holeAdjacentInteriorFaces_iff face.1).1 face.2⟩
  have hinjective : Function.Injective inclusion := by
    intro left right heq
    apply Subtype.ext
    exact embedded.internalFaceToFull_injective
      (congrArg Subtype.val heq)
  have hcard := Fintype.card_le_of_injective inclusion hinjective
  have hcard' : embedded.holeAdjacentInteriorFaces.card ≤
      embedded.holeAdjacentFullFaces.card := by
    simpa only [Fintype.card_coe] using hcard
  exact hcard'.trans embedded.card_holeAdjacentFullFaces_le_holePerimeter

/-- All internal faces that cannot belong to a full-face clean slab: the
closed neighborhood of an internal nonhexagon, or a face touching a hole. -/
def corridorForbiddenFaces {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Finset (AmbientFace embedded.cellulation.interiorFaces) :=
  faceDefectClosedNeighborhood
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces ∪
    embedded.holeAdjacentInteriorFaces

/-- The explicit number of path positions charged to either internal
curvature contamination or contact with one of the two hole faces. -/
def boundaryCleanContaminationBudget {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Nat :=
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  (2 * weight + rho) * (weight + 7) + embedded.cellulation.holePerimeter

theorem card_corridorForbiddenFaces_le_boundaryCleanContaminationBudget
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.corridorForbiddenFaces.card ≤
      embedded.boundaryCleanContaminationBudget := by
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  have hfaceSize : ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ weight + 6 := by
    intro face hface
    exact embedded.internalFaceBoundary_card_le_weight_add_six hface
  have hdefects :
      (faceDefectSet
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).card ≤ 2 * weight + rho := by
    simpa [faceDefectSet, interiorFaceDefectSet, weight, rho] using
      embedded.card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
        hsource geometry
  have hclosed :
      (faceDefectClosedNeighborhood
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).card ≤
          (2 * weight + rho) * (weight + 7) := by
    calc
      (faceDefectClosedNeighborhood
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).card ≤
          (faceDefectSet
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces).card * ((weight + 6) + 1) :=
        card_faceDefectClosedNeighborhood_le_mul_degreeBound_add_one
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces
          embedded.internalFace_incidence_le_two (weight + 6) hfaceSize
      _ ≤ (2 * weight + rho) * ((weight + 6) + 1) :=
        Nat.mul_le_mul_right ((weight + 6) + 1) hdefects
      _ = (2 * weight + rho) * (weight + 7) := by ring
  calc
    embedded.corridorForbiddenFaces.card ≤
        (faceDefectClosedNeighborhood
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          embedded.cellulation.interiorFaces).card +
          embedded.holeAdjacentInteriorFaces.card := by
      simpa [corridorForbiddenFaces] using
        (Finset.card_union_le
          (faceDefectClosedNeighborhood
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces)
          embedded.holeAdjacentInteriorFaces)
    _ ≤ (2 * weight + rho) * (weight + 7) +
          embedded.cellulation.holePerimeter :=
      Nat.add_le_add hclosed
        embedded.card_holeAdjacentInteriorFaces_le_holePerimeter
    _ = embedded.boundaryCleanContaminationBudget := by
      simp [boundaryCleanContaminationBudget, weight, rho]

/-- Face-count threshold for a clean block that is separated from both hole
faces and clean in the full quotient facial dual. -/
def boundaryCleanHexBlockThreshold {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) : Nat :=
  let weight := embedded.interiorNegativeCurvatureWeight
  (weight + 7) ^
    (((embedded.boundaryCleanContaminationBudget + 1) * blockLength) - 1)

/-- Corrected framed L1 conclusion.  The path lives in the annular internal
dual, but every selected face and every neighbor in the full quotient facial
dual is hexagonal.  In particular, the block does not touch either container
hole and can feed the translation-invariant slab/transfer layer. -/
def HasBoundaryCleanHexagonalGeodesicBlock {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) (blockLength : Nat) : Prop :=
  ∃ start finish : AmbientFace embedded.cellulation.interiorFaces,
    ∃ path : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Walk start finish,
      path.IsPath ∧
        path.length =
          (interiorDualGraph
            (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces).dist start finish ∧
        (embedded.boundaryCleanContaminationBudget + 1) * blockLength ≤
          path.length + 1 ∧
        ∃ block : Fin (embedded.boundaryCleanContaminationBudget + 1),
          ∀ offset : Fin blockLength,
            let position := corridorBlockIndex
              (defectBudget := embedded.boundaryCleanContaminationBudget)
              block offset
            let selected := path.getVert position.val
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem
              selected.1).card = 6 ∧
            ∀ neighbor : AmbientFace (Finset.univ : Finset
                (OrbitFace embedded.cellulation.rotation.toRotationSystem)),
              (interiorDualGraph
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
                  (embedded.internalFaceToFull selected) neighbor →
                (orbitFaceBoundary
                  embedded.cellulation.rotation.toRotationSystem
                  neighbor.1).card = 6

/-- Boundary-aware weighted L1.  The additional contamination term is the
actual hole perimeter, so no internal path position adjacent to a container
face is mistaken for a full translation-invariant corridor position. -/
theorem exists_boundaryCleanHexagonalGeodesicBlock_of_weightedL9
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.boundaryCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let boundary := orbitFaceBoundary RS
  let internalFaces := embedded.cellulation.interiorFaces
  let internalDual := interiorDualGraph boundary internalFaces
  let weight := embedded.interiorNegativeCurvatureWeight
  let badBudget := embedded.boundaryCleanContaminationBudget
  have hfaceSize : ∀ face ∈ internalFaces,
      (boundary face).card ≤ weight + 6 := by
    intro face hface
    exact embedded.internalFaceBoundary_card_le_weight_add_six hface
  have hlarge' :
      (weight + 7) ^ (((badBudget + 1) * blockLength) - 1) <
        internalFaces.card := by
    simpa [boundaryCleanHexBlockThreshold, weight, badBudget, internalFaces]
      using hlarge
  obtain ⟨start, finish, path, hpath, hgeodesic, hpathLength⟩ :=
    exists_geodesicPath_length_ge_of_pow_lt_card
      internalDual geometry.internalDualConnected (weight + 6)
        (((badBudget + 1) * blockLength) - 1)
      (fun face =>
        (interiorDualGraph_degree_le_faceBoundary_card
          boundary internalFaces embedded.internalFace_incidence_le_two face).trans
            (hfaceSize face.1 face.2))
      (by simpa [internalDual, Nat.add_assoc] using hlarge')
  have hpositionCount : (badBudget + 1) * blockLength ≤
      path.length + 1 := by
    omega
  have hforbidden : embedded.corridorForbiddenFaces.card ≤ badBudget := by
    simpa [badBudget] using
      embedded.card_corridorForbiddenFaces_le_boundaryCleanContaminationBudget
        hsource geometry
  have hbad :
      (pathMarkedPositions boundary internalFaces
        embedded.corridorForbiddenFaces path
        ((badBudget + 1) * blockLength)).card ≤ badBudget :=
    (card_pathMarkedPositions_le boundary internalFaces
      embedded.corridorForbiddenFaces path hpath _ hpositionCount).trans
        hforbidden
  obtain ⟨block, hblock⟩ := exists_corridorBlock_avoiding
    badBudget blockLength hpositive
      (pathMarkedPositions boundary internalFaces
        embedded.corridorForbiddenFaces path
        ((badBudget + 1) * blockLength)) hbad
  refine ⟨start, finish, path, hpath, hgeodesic, hpositionCount, block, ?_⟩
  intro offset
  let position := corridorBlockIndex (defectBudget := badBudget) block offset
  let selected := path.getVert position.val
  have hselectedClean : selected ∉ embedded.corridorForbiddenFaces := by
    intro hmarked
    exact hblock offset
      ((mem_pathMarkedPositions_iff boundary internalFaces
        embedded.corridorForbiddenFaces path
        ((badBudget + 1) * blockLength) position).2 hmarked)
  have hselectedNotDefectNeighborhood :
      selected ∉ faceDefectClosedNeighborhood boundary internalFaces := by
    intro hmarked
    exact hselectedClean (Finset.mem_union_left _ hmarked)
  have hselectedNotHoleAdjacent :
      selected ∉ embedded.holeAdjacentInteriorFaces := by
    intro hmarked
    exact hselectedClean (Finset.mem_union_right _ hmarked)
  constructor
  · by_contra hnonhex
    exact hselectedNotDefectNeighborhood
      (mem_faceDefectClosedNeighborhood_of_defect
        boundary internalFaces selected hnonhex)
  · intro neighbor hadj
    have hneighborNotHole : neighbor.1 ∉ embedded.cellulation.holeFaces := by
      intro hhole
      apply hselectedNotHoleAdjacent
      apply (embedded.mem_holeAdjacentInteriorFaces_iff selected).2
      apply Finset.mem_biUnion.2
      refine ⟨neighbor.1, hhole, ?_⟩
      simpa [holeAdjacentFullFaces, RS, boundary] using hadj.symm
    have hneighborInternal : neighbor.1 ∈ internalFaces := by
      simp [internalFaces,
        GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.interiorFaces,
        hneighborNotHole]
    let internalNeighbor : AmbientFace internalFaces :=
      ⟨neighbor.1, hneighborInternal⟩
    have hadjInternal : internalDual.Adj selected internalNeighbor := by
      rcases (interiorDualGraph_adj_iff boundary
        (Finset.univ : Finset (OrbitFace RS))).1 hadj with
          ⟨hne, edge, _hfull, hselected, hneighbor⟩
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          boundary internalFaces embedded.internalFace_incidence_le_two
            hne hselected hneighbor
    by_contra hnonhex
    apply hselectedNotDefectNeighborhood
    exact mem_faceDefectClosedNeighborhood_of_adj_defect
      boundary internalFaces hadjInternal hnonhex

/-- A boundary-clean annular block is already a clean corridor skeleton on
the full quotient-face carrier.  This is the exact adapter into the existing
finite-interface slab and transfer stack. -/
theorem nonempty_cleanOrbitHexCorridorSkeleton_of_boundaryCleanBlock
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (blockLength : Nat)
    (hclean : embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength) := by
  classical
  rcases hclean with
    ⟨start, finish, path, hpath, hgeodesic, hpositionCount, block, hblock⟩
  let RS := embedded.cellulation.rotation.toRotationSystem
  let boundary := orbitFaceBoundary RS
  let internalFaces := embedded.cellulation.interiorFaces
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let internalDual := interiorDualGraph boundary internalFaces
  let fullDual := interiorDualGraph boundary allFaces
  let badBudget := embedded.boundaryCleanContaminationBudget
  have hpositionCount' : (badBudget + 1) * blockLength ≤
      path.length + 1 := by
    simpa [badBudget] using hpositionCount
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
        (path.getVert
          (corridorBlockIndex (defectBudget := badBudget) block offset).val)
    faceAt_injective := by
      intro left right hfaces
      have hvertices :
          path.getVert
              (corridorBlockIndex
                (defectBudget := badBudget) block left).val =
            path.getVert
              (corridorBlockIndex
                (defectBudget := badBudget) block right).val :=
        embedded.internalFaceToFull_injective hfaces
      have hleftBound :
          (corridorBlockIndex
            (defectBudget := badBudget) block left).val ≤ path.length := by
        have hindex := (corridorBlockIndex
          (defectBudget := badBudget) block left).isLt
        omega
      have hrightBound :
          (corridorBlockIndex
            (defectBudget := badBudget) block right).val ≤ path.length := by
        have hindex := (corridorBlockIndex
          (defectBudget := badBudget) block right).isLt
        omega
      have hindices := hpath.getVert_injOn
        (by simpa using hleftBound) (by simpa using hrightBound) hvertices
      apply Fin.ext
      change block.val * blockLength + left.val =
        block.val * blockLength + right.val at hindices
      omega
    hexagonal := by
      intro offset
      exact (hblock offset).1
    consecutive_adjacent := by
      intro left right hsuccessor
      have hrightBound :
          (corridorBlockIndex
            (defectBudget := badBudget) block right).val ≤ path.length := by
        have hindex := (corridorBlockIndex
          (defectBudget := badBudget) block right).isLt
        omega
      have hleftStrict :
          (corridorBlockIndex
            (defectBudget := badBudget) block left).val < path.length := by
        change block.val * blockLength + left.val < path.length
        change block.val * blockLength + right.val ≤ path.length at hrightBound
        omega
      apply (hadj_iff _ _).1
      have hadj := path.adj_getVert_succ hleftStrict
      change internalDual.Adj
        (path.getVert (block.val * blockLength + left.val))
        (path.getVert (block.val * blockLength + right.val))
      change internalDual.Adj
        (path.getVert (block.val * blockLength + left.val))
        (path.getVert ((block.val * blockLength + left.val) + 1)) at hadj
      simpa only [hsuccessor, Nat.add_assoc] using hadj
    separated_not_adjacent := by
      intro left right hseparated hfull
      have hleftBound :
          (corridorBlockIndex
            (defectBudget := badBudget) block left).val ≤ path.length := by
        have hindex := (corridorBlockIndex
          (defectBudget := badBudget) block left).isLt
        omega
      have hrightBound :
          (corridorBlockIndex
            (defectBudget := badBudget) block right).val ≤ path.length := by
        have hindex := (corridorBlockIndex
          (defectBudget := badBudget) block right).isLt
        omega
      apply (not_adj_getVert_of_length_eq_dist_of_add_one_lt
        path hgeodesic
        (corridorBlockIndex
          (defectBudget := badBudget) block left).val
        (corridorBlockIndex
          (defectBudget := badBudget) block right).val
        hleftBound hrightBound (by
          change block.val * blockLength + left.val + 1 <
            block.val * blockLength + right.val
          omega))
      exact (hadj_iff _ _).2 hfull
  }
  exact ⟨{
    toOrbitHexCorridorSkeleton := corridor
    neighbor_hexagonal := by
      intro offset neighbor hadj
      exact (hblock offset).2 neighbor hadj
  }⟩

/-- Complete boundary-aware framed L1 adapter into the full clean-corridor
stack. -/
theorem nonempty_cleanOrbitHexCorridorSkeleton_of_weightedL9
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.boundaryCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength) :=
  embedded.nonempty_cleanOrbitHexCorridorSkeleton_of_boundaryCleanBlock
    blockLength
      (embedded.exists_boundaryCleanHexagonalGeodesicBlock_of_weightedL9
        hsource geometry blockLength hpositive hlarge)

/-- Coarse weight bound supplied by a proposed bound on internal pentagons. -/
def pentagonBoundedBoundaryCleanWeightBound
    (source : SourceTrail G) (pentagonBound : Nat) : Nat :=
  pentagonBound + 4 + 2 * source.frozenInterfaceStubVertices.card

/-- Coarse full-face contamination budget under a pentagon bound.  Exact L9
bounds both `W` and `rho` by the same weight bound; the actual hole perimeter
is then at most twice the frozen-stub count plus that bound. -/
def pentagonBoundedBoundaryCleanContaminationBudget
    (source : SourceTrail G) (pentagonBound : Nat) : Nat :=
  let weightBound :=
    pentagonBoundedBoundaryCleanWeightBound source pentagonBound
  (3 * weightBound) * (weightBound + 7) +
    (2 * source.frozenInterfaceStubVertices.card + weightBound)

/-- Uniform boundary-clean L1 threshold at a proposed pentagon bound.  The
exponent deliberately omits the harmless predecessor used by the sharp
threshold, making monotonicity explicit. -/
def pentagonBoundedBoundaryCleanHexBlockThreshold
    (source : SourceTrail G) (pentagonBound blockLength : Nat) : Nat :=
  let weightBound :=
    pentagonBoundedBoundaryCleanWeightBound source pentagonBound
  let contaminationBound :=
    pentagonBoundedBoundaryCleanContaminationBudget source pentagonBound
  (weightBound + 7) ^ ((contaminationBound + 1) * blockLength)

/-- Complete honest framed L1 alternative.  Above a threshold depending only
on the proposed pentagon bound and the fixed source interface, either that
bound is false or the existing full-face clean-corridor transfer carrier is
present.  The first branch is the remaining high-curvature structural
obligation of the reductive proof. -/
theorem pentagonCount_exceeds_bound_or_nonempty_cleanOrbitHexCorridorSkeleton
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge :
      pentagonBoundedBoundaryCleanHexBlockThreshold source
          pentagonBound blockLength <
        embedded.cellulation.interiorFaces.card) :
    pentagonBound < embedded.interiorFaceLengths.count 5 ∨
      Nonempty (CleanOrbitHexCorridorSkeleton
        embedded.cellulation.rotation.toRotationSystem blockLength) := by
  let pentagons := embedded.interiorFaceLengths.count 5
  let weight := embedded.interiorNegativeCurvatureWeight
  let rho := embedded.cellulation.boundarySurplus source.toFramedTrailData
  let stubCount := source.frozenInterfaceStubVertices.card
  let weightBound :=
    pentagonBoundedBoundaryCleanWeightBound source pentagonBound
  let contaminationBound :=
    pentagonBoundedBoundaryCleanContaminationBudget source pentagonBound
  by_cases hpentagons : pentagons ≤ pentagonBound
  · right
    have hbalance :=
      embedded.interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
        hsource geometry
    have hweight : weight ≤ weightBound := by
      dsimp [pentagons, weight, rho, stubCount] at hbalance hpentagons
      dsimp [weight, weightBound, stubCount,
        pentagonBoundedBoundaryCleanWeightBound]
      omega
    have hrho : rho ≤ weightBound := by
      dsimp [pentagons, weight, rho, stubCount] at hbalance hpentagons
      dsimp [rho, weightBound, stubCount,
        pentagonBoundedBoundaryCleanWeightBound]
      omega
    have hholeEq : embedded.cellulation.holePerimeter =
        2 * stubCount + rho := by
      simpa [stubCount, rho, toFramedTrailData] using
        (embedded.cellulation
          |>.holePerimeter_eq_twice_frozenStubCount_add_boundarySurplus
            source.toFramedTrailData
              embedded.twice_frozenStubCount_le_holePerimeter)
    have hhole : embedded.cellulation.holePerimeter ≤
        2 * stubCount + weightBound := by
      omega
    have hfirstFactor : 2 * weight + rho ≤ 3 * weightBound := by
      omega
    have hsecondFactor : weight + 7 ≤ weightBound + 7 := by
      omega
    have hproduct :
        (2 * weight + rho) * (weight + 7) ≤
          (3 * weightBound) * (weightBound + 7) :=
      Nat.mul_le_mul hfirstFactor hsecondFactor
    have hcontamination :
        embedded.boundaryCleanContaminationBudget ≤ contaminationBound := by
      unfold boundaryCleanContaminationBudget
      dsimp [contaminationBound,
        pentagonBoundedBoundaryCleanContaminationBudget]
      exact Nat.add_le_add hproduct hhole
    have hbase : weight + 7 ≤ weightBound + 7 := by omega
    have hexponent :
        ((embedded.boundaryCleanContaminationBudget + 1) * blockLength) - 1 ≤
          (contaminationBound + 1) * blockLength := by
      exact (Nat.sub_le _ _).trans
        (Nat.mul_le_mul_right blockLength
          (Nat.add_le_add_right hcontamination 1))
    have hthreshold :
        embedded.boundaryCleanHexBlockThreshold blockLength ≤
          pentagonBoundedBoundaryCleanHexBlockThreshold source
            pentagonBound blockLength := by
      calc
        embedded.boundaryCleanHexBlockThreshold blockLength =
            (weight + 7) ^
              (((embedded.boundaryCleanContaminationBudget + 1) *
                blockLength) - 1) := by
          simp [boundaryCleanHexBlockThreshold, weight]
        _ ≤ (weightBound + 7) ^
              (((embedded.boundaryCleanContaminationBudget + 1) *
                blockLength) - 1) :=
          Nat.pow_le_pow_left hbase _
        _ ≤ (weightBound + 7) ^
              ((contaminationBound + 1) * blockLength) :=
          Nat.pow_le_pow_right (by omega) hexponent
        _ = pentagonBoundedBoundaryCleanHexBlockThreshold source
              pentagonBound blockLength := by
          simp [pentagonBoundedBoundaryCleanHexBlockThreshold,
            weightBound, contaminationBound]
    apply embedded.nonempty_cleanOrbitHexCorridorSkeleton_of_weightedL9
      hsource geometry blockLength hpositive
    exact lt_of_le_of_lt hthreshold hlarge
  · left
    simpa [pentagons] using (Nat.lt_of_not_ge hpentagons)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
