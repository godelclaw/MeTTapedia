import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCorridor

/-!
# Boundary-clean L1 corridors for the Cell-3 closed-web carrier

The ordinary Cell-3 L1 extraction finds a hexagonal block in the induced
annular facial dual.  That alone does not say that a selected cell avoids the
two named holes in the full facial dual.  Addendum XXVII(iii) needs exactly
that stronger fact: both holes and the defect zone must lie outside the
pumped region.

This module charges the full-dual neighborhoods of the two holes to their
literal perimeter, combines that cost with the source's weighted defect
budget, and extracts a clean block avoiding both.  It is stated directly for
`ClosedWebAnnularEmbedding`, the Cell-3 source carrier; no framed-trail
conversion is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAnnularEmbedding

open GoertzelV24AnnularFrontierExcess.AnnularFrontierEmbeddingExcess
open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24BoundedDegreePath
open GoertzelV24BulkCorridor
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexPathExtraction
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

variable {data : AnnularBoundaryData G outerCount}

namespace ClosedWebAnnularEmbedding

/-- Include an internal annular face into the full quotient-face carrier. -/
def internalFaceToFull (embedded : ClosedWebAnnularEmbedding data)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
  ⟨face.1, Finset.mem_univ _⟩

theorem internalFaceToFull_injective (embedded : ClosedWebAnnularEmbedding data) :
    Function.Injective embedded.internalFaceToFull := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun face => face.1) heq

/-- Full-dual faces adjacent to one of the two literal hole faces. -/
def holeAdjacentFullFaces (embedded : ClosedWebAnnularEmbedding data) :
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

/-- Internal faces that touch a named hole in the full facial dual. -/
def holeAdjacentInteriorFaces (embedded : ClosedWebAnnularEmbedding data) :
    Finset (AmbientFace embedded.cellulation.interiorFaces) :=
  Finset.univ.filter fun face =>
    embedded.internalFaceToFull face ∈ embedded.holeAdjacentFullFaces

@[simp]
theorem mem_holeAdjacentInteriorFaces_iff
    (embedded : ClosedWebAnnularEmbedding data)
    (face : AmbientFace embedded.cellulation.interiorFaces) :
    face ∈ embedded.holeAdjacentInteriorFaces ↔
      embedded.internalFaceToFull face ∈ embedded.holeAdjacentFullFaces := by
  simp [holeAdjacentInteriorFaces]

/-- The full-dual neighborhood of the two holes is bounded by their literal
facial perimeter.  Repeated boundary occurrences only make this estimate
looser, never unsound. -/
theorem card_holeAdjacentFullFaces_le_holePerimeter
    (embedded : ClosedWebAnnularEmbedding data) :
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
    (embedded : ClosedWebAnnularEmbedding data) :
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

/-- Faces forbidden to a Cell-3 pumping block: a defect or neighbor of one,
or a face adjacent in the full dual to either named hole. -/
def corridorForbiddenFaces (embedded : ClosedWebAnnularEmbedding data) :
    Finset (AmbientFace embedded.cellulation.interiorFaces) :=
  faceDefectClosedNeighborhood
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces ∪
    embedded.holeAdjacentInteriorFaces

/-- The finite number of path positions excluded by the source's defect
budget together with its literal hole perimeter. -/
def boundaryCleanContaminationBudget (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  let weight := interiorNegativeCurvatureWeight embedded
  let rho := boundarySurplus embedded
  (2 * weight + rho) * (weight + 7) + embedded.cellulation.holePerimeter

theorem card_corridorForbiddenFaces_le_boundaryCleanContaminationBudget
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    embedded.corridorForbiddenFaces.card ≤
      embedded.boundaryCleanContaminationBudget := by
  let weight := interiorNegativeCurvatureWeight embedded
  let rho := boundarySurplus embedded
  have hfaceSize : ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ weight + 6 := by
    intro face hface
    exact internalFaceBoundary_card_le_weight_add_six embedded hface
  have hdefects :
      (faceDefectSet
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).card ≤ 2 * weight + rho := by
    simpa [faceDefectSet, interiorFaceDefectSet] using
      card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
        embedded hdata geometry
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
          (internalFace_incidence_le_two embedded) (weight + 6) hfaceSize
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

/-- Face-count threshold for a Cell-3 block that is clean in the full dual
and separated from both named holes. -/
def boundaryCleanHexBlockThreshold
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat) : Nat :=
  let weight := interiorNegativeCurvatureWeight embedded
  (weight + 7) ^
    (((embedded.boundaryCleanContaminationBudget + 1) * blockLength) - 1)

/-- The local full-dual cleanliness condition at one selected block of an
annular facial-dual path.  Naming it keeps the source realization carrier
small while retaining exactly the L1 certificate used by the corridor. -/
def BoundaryCleanHexagonalBlockAt
    (embedded : ClosedWebAnnularEmbedding data)
    {start finish : AmbientFace embedded.cellulation.interiorFaces}
    (path : (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Walk start finish)
    (blockLength : Nat)
    (block : Fin (embedded.boundaryCleanContaminationBudget + 1)) : Prop :=
  ∀ offset : Fin blockLength,
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

/-- A Cell-3 clean block whose selected faces and all full-dual neighbors are
hexagonal internal faces.  This is the exact L1 form required before those
faces may be used as a pumped corridor. -/
def HasBoundaryCleanHexagonalGeodesicBlock
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat) : Prop :=
  ∃ start finish : AmbientFace embedded.cellulation.interiorFaces,
    ∃ path : (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces).Walk start finish,
      path.IsPath ∧
        path.length =
          (interiorDualGraph
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem)
            embedded.cellulation.interiorFaces).dist start finish ∧
        (embedded.boundaryCleanContaminationBudget + 1) * blockLength ≤
            path.length + 1 ∧
        ∃ block : Fin (embedded.boundaryCleanContaminationBudget + 1),
          embedded.BoundaryCleanHexagonalBlockAt path blockLength block

/-- Boundary-aware weighted L1 for the actual Cell-3 annulus.  The added
contamination cost is the literal hole perimeter, so no selected position can
quietly touch a hole when later used to form a splice boundary. -/
theorem exists_boundaryCleanHexagonalGeodesicBlock_of_weightedAnnularExcess
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.boundaryCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let boundary := orbitFaceBoundary RS
  let internalFaces := embedded.cellulation.interiorFaces
  let internalDual := interiorDualGraph boundary internalFaces
  let weight := interiorNegativeCurvatureWeight embedded
  let badBudget := embedded.boundaryCleanContaminationBudget
  have hfaceSize : ∀ face ∈ internalFaces,
      (boundary face).card ≤ weight + 6 := by
    intro face hface
    exact internalFaceBoundary_card_le_weight_add_six embedded hface
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
          boundary internalFaces (internalFace_incidence_le_two embedded) face).trans
            (hfaceSize face.1 face.2))
      (by simpa [internalDual, Nat.add_assoc] using hlarge')
  have hpositionCount : (badBudget + 1) * blockLength ≤
      path.length + 1 := by
    omega
  have hforbidden : embedded.corridorForbiddenFaces.card ≤ badBudget := by
    simpa [badBudget] using
      embedded.card_corridorForbiddenFaces_le_boundaryCleanContaminationBudget
        hdata geometry
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
          boundary internalFaces (internalFace_incidence_le_two embedded)
            hne hselected hneighbor
    refine ⟨hneighborInternal, ?_⟩
    by_contra hnonhex
    apply hselectedNotDefectNeighborhood
    exact mem_faceDefectClosedNeighborhood_of_adj_defect
      boundary internalFaces hadjInternal hnonhex

/-- A Cell-3 corridor together with the part of L1 that a bare clean skeleton
does not remember: every full-dual neighbour of every selected corridor face
is an annular interior face.  This is the precise ``both holes lie outside
the pumped region'' invariant needed when local layer walks are assembled.

Keeping this information on the source carrier avoids the invalid shortcut of
inferring it merely from hexagonality: a named hole could itself have length
six. -/
structure BoundaryCleanOrbitHexCorridor
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat) where
  toCleanOrbitHexCorridorSkeleton :
    CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength
  face_internal : ∀ offset : Fin blockLength,
    (toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt offset).1 ∈
      embedded.cellulation.interiorFaces
  neighbor_internal : ∀ offset : Fin blockLength,
    ∀ neighbor : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)),
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt offset)
          neighbor →
        neighbor.1 ∈ embedded.cellulation.interiorFaces

/-- The bare finite corridor skeleton is actually the literal clean interval
selected by Cell-3 L1.  Keeping this as a proposition rather than duplicating
the full dependent path witness in the finite carrier keeps the compiled
interface small while still exposing the geodesic when remote separation is
proved. -/
def SourceRealizesBoundaryCleanOrbitHexCorridor
    (embedded : ClosedWebAnnularEmbedding data) (blockLength : Nat)
    (corridor : BoundaryCleanOrbitHexCorridor embedded blockLength) : Prop :=
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
          embedded.BoundaryCleanHexagonalBlockAt path blockLength block ∧
            ∀ offset : Fin blockLength,
              corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
                offset =
                embedded.internalFaceToFull
                  (path.getVert
                    (corridorBlockIndex
                      (defectBudget := embedded.boundaryCleanContaminationBudget)
                      block offset).val)

/-- A boundary-clean Cell-3 block supplies a literal clean corridor skeleton
in the full quotient-face carrier, together with the specific source geodesic
from which it came.  This does not introduce an arbitrary transversal. -/
theorem exists_sourceRealizedBoundaryCleanOrbitHexCorridor_of_boundaryCleanBlock
    (embedded : ClosedWebAnnularEmbedding data)
    (blockLength : Nat)
    (hclean : embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    ∃ corridor : BoundaryCleanOrbitHexCorridor embedded blockLength,
      embedded.SourceRealizesBoundaryCleanOrbitHexCorridor blockLength corridor := by
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
          boundary internalFaces (internalFace_incidence_le_two embedded)
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
  refine ⟨{
    toCleanOrbitHexCorridorSkeleton := {
      toOrbitHexCorridorSkeleton := corridor
      neighbor_hexagonal := by
        intro offset neighbor hadj
        exact ((hblock offset).2 neighbor hadj).2
    }
    face_internal := by
      intro offset
      exact (path.getVert
        (corridorBlockIndex (defectBudget := badBudget) block offset).val).2
    neighbor_internal := by
      intro offset neighbor hadj
      exact ((hblock offset).2 neighbor hadj).1
  }, start, finish, path, hpath, hgeodesic, hpositionCount, block, hblock, ?_⟩
  intro offset
  rfl

/-- The weighted Cell-3 clean-block estimate directly supplies a
source-realized boundary-clean dual geodesic.  This packages the quantitative
extraction and its literal witness together; it does not yet certify the
source's full ladder incidence, construct transverse crosscuts, or form a
splice. -/
theorem exists_sourceRealizedBoundaryCleanOrbitHexCorridor_of_weightedAnnularExcess
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded)
    (blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : embedded.boundaryCleanHexBlockThreshold blockLength <
      embedded.cellulation.interiorFaces.card) :
    ∃ corridor : BoundaryCleanOrbitHexCorridor embedded blockLength,
      embedded.SourceRealizesBoundaryCleanOrbitHexCorridor blockLength corridor := by
  exact embedded.exists_sourceRealizedBoundaryCleanOrbitHexCorridor_of_boundaryCleanBlock
    blockLength
    (embedded.exists_boundaryCleanHexagonalGeodesicBlock_of_weightedAnnularExcess
      hdata geometry blockLength hpositive hlarge)

/-- Forgetting the retained source-geodesic witness recovers the earlier
nonempty finite-interface corridor result. -/
theorem nonempty_boundaryCleanOrbitHexCorridor_of_boundaryCleanBlock
    (embedded : ClosedWebAnnularEmbedding data)
    (blockLength : Nat)
    (hclean : embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    Nonempty (BoundaryCleanOrbitHexCorridor embedded blockLength) := by
  rcases embedded.exists_sourceRealizedBoundaryCleanOrbitHexCorridor_of_boundaryCleanBlock
      blockLength hclean with ⟨corridor, _⟩
  exact ⟨corridor⟩

/-- A full-dual face cannot meet two selected Cell-3 corridor positions more
than two steps apart.  Boundary cleanliness returns such a face to the
internal annular dual, and the retained L1 geodesic then rules out the
resulting two-step shortcut.  Thus remote layer intersections reduce to the
bounded local window described by the source's rail cases. -/
theorem BoundaryCleanOrbitHexCorridor.no_common_fullNeighbor_of_add_two_lt
    {embedded : ClosedWebAnnularEmbedding data} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor embedded blockLength)
    (hsource : embedded.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (left right : Fin blockLength) (hseparated : left.val + 2 < right.val) :
    ¬ ∃ neighbor : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)),
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt left) neighbor ∧
        (interiorDualGraph
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          (corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton.faceAt right) neighbor := by
  rcases hsource with
    ⟨start, finish, path, hpath, hgeodesic, hpositionCount, block, hblock,
      hfaceAt⟩
  rintro ⟨neighbor, hleft, hright⟩
  rw [hfaceAt left] at hleft
  rw [hfaceAt right] at hright
  let boundary := orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
  let internalFaces := embedded.cellulation.interiorFaces
  let allFaces : Finset (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
    Finset.univ
  let internalDual := interiorDualGraph boundary internalFaces
  let leftIndex := corridorBlockIndex
    (defectBudget := embedded.boundaryCleanContaminationBudget)
    block left
  let rightIndex := corridorBlockIndex
    (defectBudget := embedded.boundaryCleanContaminationBudget)
    block right
  have hneighborInternal : neighbor.1 ∈ internalFaces := by
    exact ((hblock left).2 neighbor hleft).1
  let internalNeighbor : AmbientFace internalFaces :=
    ⟨neighbor.1, hneighborInternal⟩
  have hleftInternal : internalDual.Adj
      (path.getVert leftIndex.val) internalNeighbor := by
    rcases (interiorDualGraph_adj_iff boundary allFaces).1 hleft with
      ⟨hne, edge, _hinterior, hleftEdge, hneighborEdge⟩
    exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      boundary internalFaces (internalFace_incidence_le_two embedded)
      hne hleftEdge (by simpa [internalNeighbor] using hneighborEdge)
  have hrightInternal : internalDual.Adj
      (path.getVert rightIndex.val) internalNeighbor := by
    rcases (interiorDualGraph_adj_iff boundary allFaces).1 hright with
      ⟨hne, edge, _hinterior, hrightEdge, hneighborEdge⟩
    exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      boundary internalFaces (internalFace_incidence_le_two embedded)
      hne hrightEdge (by simpa [internalNeighbor] using hneighborEdge)
  have hleftBound : leftIndex.val ≤ path.length := by
    have hindex := leftIndex.isLt
    dsimp [leftIndex, corridorBlockIndex] at hindex ⊢
    omega
  have hrightBound : rightIndex.val ≤ path.length := by
    have hindex := rightIndex.isLt
    dsimp [rightIndex, corridorBlockIndex] at hindex ⊢
    omega
  apply not_exists_common_neighbor_getVert_of_length_eq_dist_of_add_two_lt
    path hgeodesic leftIndex.val rightIndex.val
    hleftBound hrightBound
  · change block.val * blockLength + left.val + 2 <
      block.val * blockLength + right.val
    omega
  · exact ⟨internalNeighbor, hleftInternal, hrightInternal.symm⟩

/-- Forgetting the annular-interior half of a Cell-3 clean corridor recovers
the earlier finite-interface corridor carrier. -/
theorem nonempty_cleanOrbitHexCorridorSkeleton_of_boundaryCleanBlock
    (embedded : ClosedWebAnnularEmbedding data)
    (blockLength : Nat)
    (hclean : embedded.HasBoundaryCleanHexagonalGeodesicBlock blockLength) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem blockLength) := by
  rcases embedded.nonempty_boundaryCleanOrbitHexCorridor_of_boundaryCleanBlock
      blockLength hclean with ⟨corridor⟩
  exact ⟨corridor.toCleanOrbitHexCorridorSkeleton⟩

end ClosedWebAnnularEmbedding

end

end GoertzelV24ClosedWebAnnularEmbedding

end Mettapedia.GraphTheory.FourColor
