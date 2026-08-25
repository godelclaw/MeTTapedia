import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLengthDepth

/-!
# Source-derived contaminated cuts on a closed-web radial path

Addendum XXVII's L6 pigeonhole takes a finite set of contaminated
transversal positions.  This module constructs that set from the actual
annular faces instead of accepting an arbitrary caller-supplied set.

A cut immediately after radial-path vertex `i` is marked when its path edge
lies on a face forbidden by the source cleanliness condition: a defect, a
neighbor of a defect, or a face adjacent to either named hole.  Simplicity of
the radial path makes distinct cut positions use distinct edges.  The number
of marked cuts is therefore bounded by the total edge support of the forbidden
faces, and hence by the weighted-curvature and hole-perimeter budget already
proved for the source annulus.

This is the contamination-set input to L6.  It does not turn an avoiding
block into the final source splice corridor; that realization remains a
separate geometric theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialDefectPositions

open GoertzelV24BulkCorridor
open GoertzelV24AnnularFrontierExcess.AnnularFrontierEmbeddingExcess
open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24BoundedDegreePath
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebSectorAlternation
open GoertzelV24ClosedWebSourceLengthDepth
open GoertzelV24ClosedWebSourceLengthDepth.Instance
open GoertzelV24CleanHexCorridor
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

variable {data : AnnularBoundaryData G outerCount}

/-- Actual primal edges carried by all faces excluded from a source-clean
radial block. -/
def radialForbiddenEdgeSupport (embedded : ClosedWebAnnularEmbedding data) :
    Finset G.edgeSet := by
  classical
  exact embedded.corridorForbiddenFaces.biUnion fun face =>
    orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face.1

/-- Total boundary length of the actual internal nonhexagonal faces, written
on the ambient-face subtype used by the clean-neighborhood construction. -/
def radialDefectBoundaryLength
    (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  ∑ face ∈ ambientFaceDefectSet boundary
      embedded.cellulation.interiorFaces,
    (boundary face.1).card

/-- The ambient-face presentation of defect-boundary length agrees with the
weighted-curvature multiset presentation. -/
theorem radialDefectBoundaryLength_eq_nonHexagonalBoundaryLength
    (embedded : ClosedWebAnnularEmbedding data) :
    radialDefectBoundaryLength embedded =
      nonHexagonalBoundaryLength (interiorFaceLengths embedded) := by
  classical
  rw [← sum_interiorFaceDefectSet_boundary_card_eq_nonHexagonalBoundaryLength
    embedded]
  unfold radialDefectBoundaryLength
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  dsimp only
  refine Finset.sum_bij
    (fun face _hface => face.1)
    ?_ ?_ ?_ (fun _face _hface => rfl)
  · intro face hface
    have hdefect :=
      (mem_ambientFaceDefectSet_iff boundary
        embedded.cellulation.interiorFaces face).1 hface
    exact Finset.mem_filter.2 ⟨face.2, hdefect⟩
  · intro left _hleft right _hright heq
    exact Subtype.ext heq
  · intro face hface
    have hparts := Finset.mem_filter.1 hface
    let ambient : AmbientFace embedded.cellulation.interiorFaces :=
      ⟨face, hparts.1⟩
    refine ⟨ambient, ?_, rfl⟩
    exact (mem_ambientFaceDefectSet_iff boundary
      embedded.cellulation.interiorFaces ambient).2 hparts.2

/-- Linear weighted bound for the actual internal defect-boundary length. -/
theorem radialDefectBoundaryLength_le
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    radialDefectBoundaryLength embedded ≤
      12 * interiorNegativeCurvatureWeight embedded +
        5 * boundarySurplus embedded := by
  rw [radialDefectBoundaryLength_eq_nonHexagonalBoundaryLength]
  exact nonHexagonalBoundaryLength_interiorFaceLengths_le
    embedded hdata geometry

/-- The whole closed dual neighborhood of the defects has cardinality at
most twice their total boundary length.  This sums the actual dual degrees
instead of multiplying the defect count by one global maximum face size. -/
theorem card_faceDefectClosedNeighborhood_le_two_mul_defectBoundaryLength
    (embedded : ClosedWebAnnularEmbedding data)
    (geometry : AnnularFrontierGeometry embedded) :
    (faceDefectClosedNeighborhood
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).card ≤
        2 * radialDefectBoundaryLength embedded := by
  classical
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  let allFaces := embedded.cellulation.interiorFaces
  let defects := ambientFaceDefectSet boundary allFaces
  let dual := interiorDualGraph boundary allFaces
  letI : DecidableRel dual.Adj := Classical.decRel _
  have hdegree : ∀ face : AmbientFace allFaces,
      dual.degree face ≤ (boundary face.1).card := by
    intro face
    exact interiorDualGraph_degree_le_faceBoundary_card
      boundary allFaces (internalFace_incidence_le_two embedded) face
  have hdefectCard : defects.card ≤ radialDefectBoundaryLength embedded := by
    calc
      defects.card = ∑ _face ∈ defects, 1 := by simp
      _ ≤ ∑ face ∈ defects, (boundary face.1).card := by
        apply Finset.sum_le_sum
        intro face _hface
        have hminimum := geometry.internalMinimumFive face.1 face.2
        exact (by norm_num : 1 ≤ 5).trans hminimum
      _ = radialDefectBoundaryLength embedded := by
        simp [radialDefectBoundaryLength, defects, boundary, allFaces]
  calc
    (faceDefectClosedNeighborhood boundary allFaces).card ≤
        ∑ defect ∈ defects, ((boundary defect.1).card + 1) := by
      unfold faceDefectClosedNeighborhood
      calc
        (defects.biUnion fun defect =>
            Finset.univ.filter fun face =>
              face = defect ∨ dual.Adj face defect).card ≤
            ∑ defect ∈ defects,
              (Finset.univ.filter fun face =>
                face = defect ∨ dual.Adj face defect).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ defect ∈ defects, ((boundary defect.1).card + 1) := by
          apply Finset.sum_le_sum
          intro defect _hdefect
          have hsubset :
              (Finset.univ.filter fun face : AmbientFace allFaces =>
                face = defect ∨ dual.Adj face defect) ⊆
                insert defect (dual.neighborFinset defect) := by
            intro face hface
            rcases (Finset.mem_filter.1 hface).2 with rfl | hadj
            · simp
            · exact Finset.mem_insert.2 (Or.inr (by simpa using hadj.symm))
          calc
            (Finset.univ.filter fun face : AmbientFace allFaces =>
                face = defect ∨ dual.Adj face defect).card ≤
                (insert defect (dual.neighborFinset defect)).card :=
              Finset.card_le_card hsubset
            _ ≤ dual.degree defect + 1 := by
              simp only [← SimpleGraph.card_neighborFinset_eq_degree]
              exact Finset.card_insert_le defect (dual.neighborFinset defect)
            _ ≤ (boundary defect.1).card + 1 :=
              Nat.add_le_add_right (hdegree defect) 1
    _ = radialDefectBoundaryLength embedded + defects.card := by
      simp [radialDefectBoundaryLength, defects, boundary, allFaces,
        Finset.sum_add_distrib]
    _ ≤ radialDefectBoundaryLength embedded +
        radialDefectBoundaryLength embedded :=
      Nat.add_le_add_left hdefectCard _
    _ = 2 * radialDefectBoundaryLength embedded := by omega

/-- Any selected family of internal faces pays six edges per face, plus one
global copy of the actual defect-boundary length.  Hexagons pay the first
term; every nonhexagon belongs to the global defect family. -/
theorem sum_internalFaceBoundaries_le_six_mul_card_add_defectBoundaryLength
    (embedded : ClosedWebAnnularEmbedding data)
    (faces : Finset (AmbientFace embedded.cellulation.interiorFaces)) :
    (∑ face ∈ faces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face.1).card) ≤
      6 * faces.card + radialDefectBoundaryLength embedded := by
  classical
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  let defects := ambientFaceDefectSet boundary
    embedded.cellulation.interiorFaces
  let hexFaces := faces.filter fun face => (boundary face.1).card = 6
  let defectFaces := faces.filter fun face => (boundary face.1).card ≠ 6
  have hhex :
      (∑ face ∈ hexFaces, (boundary face.1).card) =
        6 * hexFaces.card := by
    calc
      (∑ face ∈ hexFaces, (boundary face.1).card) =
          ∑ _face ∈ hexFaces, 6 := by
        apply Finset.sum_congr rfl
        intro face hface
        exact (Finset.mem_filter.1 hface).2
      _ = 6 * hexFaces.card := by simp [Nat.mul_comm]
  have hdefectSubset : defectFaces ⊆ defects := by
    intro face hface
    have hnonhex := (Finset.mem_filter.1 hface).2
    exact (mem_ambientFaceDefectSet_iff boundary
      embedded.cellulation.interiorFaces face).2 hnonhex
  have hdefectSum :
      (∑ face ∈ defectFaces, (boundary face.1).card) ≤
        radialDefectBoundaryLength embedded := by
    calc
      (∑ face ∈ defectFaces, (boundary face.1).card) ≤
          ∑ face ∈ defects, (boundary face.1).card :=
        Finset.sum_le_sum_of_subset hdefectSubset
      _ = radialDefectBoundaryLength embedded := by
        simp [radialDefectBoundaryLength, defects, boundary]
  have hpartition :
      (∑ face ∈ faces, (boundary face.1).card) =
        (∑ face ∈ hexFaces, (boundary face.1).card) +
          ∑ face ∈ defectFaces, (boundary face.1).card := by
    simpa [hexFaces, defectFaces] using
      (Finset.sum_filter_add_sum_filter_not
        (s := faces) (p := fun face => (boundary face.1).card = 6)
        (f := fun face => (boundary face.1).card)).symm
  rw [hpartition, hhex]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 6 (Finset.card_le_card (Finset.filter_subset _ _)))
    hdefectSum

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A union sum is bounded by paying each of its two inputs separately. -/
private theorem sum_union_le_add {α : Type*} [DecidableEq α]
    (left right : Finset α) (value : α → Nat) :
    (∑ item ∈ left ∪ right, value item) ≤
      (∑ item ∈ left, value item) + ∑ item ∈ right, value item := by
  classical
  let remainder := right \ left
  have hunion : left ∪ right = left ∪ remainder := by
    ext item
    by_cases hleft : item ∈ left <;> simp [remainder, hleft]
  have hdisjoint : Disjoint left remainder := by
    refine Finset.disjoint_left.2 ?_
    intro item hleft hrem
    exact (Finset.mem_sdiff.1 hrem).2 hleft
  rw [hunion, Finset.sum_union hdisjoint]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _

/-- Linear edge-incidence budget for the complete forbidden facial zone.
The coefficient is deliberately conservative.  Its important feature is
linearity in the honest negative-curvature weight, rather than the former
product of a defect-count bound and a maximum face size. -/
def radialForbiddenEdgeBudget (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  14 * (12 * interiorNegativeCurvatureWeight embedded +
    5 * boundarySurplus embedded) + 6 * embedded.cellulation.holePerimeter

/-- The forbidden-face edge union obeys the linear weighted budget.  The
proof sums actual facial incidences, charges the closed defect neighborhood
to dual degrees, and charges the two hole neighborhoods to their literal
perimeter. -/
theorem card_radialForbiddenEdgeSupport_le
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    (radialForbiddenEdgeSupport embedded).card ≤
      radialForbiddenEdgeBudget embedded := by
  classical
  let boundary := orbitFaceBoundary
    embedded.cellulation.rotation.toRotationSystem
  let closed := faceDefectClosedNeighborhood boundary
    embedded.cellulation.interiorFaces
  let holes := embedded.holeAdjacentInteriorFaces
  let defectLength := radialDefectBoundaryLength embedded
  have hclosedCard : closed.card ≤ 2 * defectLength := by
    exact card_faceDefectClosedNeighborhood_le_two_mul_defectBoundaryLength
      embedded geometry
  have hclosedSum :
      (∑ face ∈ closed, (boundary face.1).card) ≤
        13 * defectLength := by
    calc
      (∑ face ∈ closed, (boundary face.1).card) ≤
          6 * closed.card + defectLength :=
        sum_internalFaceBoundaries_le_six_mul_card_add_defectBoundaryLength
          embedded closed
      _ ≤ 6 * (2 * defectLength) + defectLength :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 6 hclosedCard) _
      _ = 13 * defectLength := by ring
  have hholeSum :
      (∑ face ∈ holes, (boundary face.1).card) ≤
        6 * embedded.cellulation.holePerimeter + defectLength := by
    calc
      (∑ face ∈ holes, (boundary face.1).card) ≤
          6 * holes.card + defectLength :=
        sum_internalFaceBoundaries_le_six_mul_card_add_defectBoundaryLength
          embedded holes
      _ ≤ 6 * embedded.cellulation.holePerimeter + defectLength :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left 6
            embedded.card_holeAdjacentInteriorFaces_le_holePerimeter) _
  have hdefectLength :
      defectLength ≤ 12 * interiorNegativeCurvatureWeight embedded +
        5 * boundarySurplus embedded := by
    exact radialDefectBoundaryLength_le embedded hdata geometry
  calc
    (radialForbiddenEdgeSupport embedded).card ≤
        ∑ face ∈ embedded.corridorForbiddenFaces,
          (boundary face.1).card := by
      unfold radialForbiddenEdgeSupport
      exact Finset.card_biUnion_le
    _ ≤ (∑ face ∈ closed, (boundary face.1).card) +
          ∑ face ∈ holes, (boundary face.1).card := by
      simpa [ClosedWebAnnularEmbedding.corridorForbiddenFaces,
        closed, holes, boundary] using
        sum_union_le_add closed holes fun face => (boundary face.1).card
    _ ≤ 13 * defectLength +
          (6 * embedded.cellulation.holePerimeter + defectLength) :=
      Nat.add_le_add hclosedSum hholeSum
    _ = 14 * defectLength + 6 * embedded.cellulation.holePerimeter := by
      ring
    _ ≤ 14 * (12 * interiorNegativeCurvatureWeight embedded +
          5 * boundarySurplus embedded) +
          6 * embedded.cellulation.holePerimeter :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 14 hdefectLength) _
    _ = radialForbiddenEdgeBudget embedded := by
      rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Positional reading of a walk edge gives the unordered pair of successive
vertices. -/
private theorem edges_get_cast_eq_s_getVert
    {start finish : V} (walk : G.Walk start finish)
    (step : Fin walk.length) :
    walk.edges.get (Fin.cast walk.length_edges.symm step) =
      s(walk.getVert step.val, walk.getVert (step.val + 1)) := by
  simp [SimpleGraph.Walk.edges, List.get_eq_getElem,
    SimpleGraph.Walk.darts_getElem_eq_getVert]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Distinct cut positions of a simple radial path carry distinct ambient
path edges. -/
theorem ambientRadialPathStepEdge_injective
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    Function.Injective (fun position : Fin radial.path.length =>
      ambientRadialPathStepEdge radial position.val position.isLt) := by
  intro left right hedge
  let ambient := ambientRadialPath radial
  let left' : Fin ambient.length :=
    Fin.cast (ambientRadialPath_length radial).symm left
  let right' : Fin ambient.length :=
    Fin.cast (ambientRadialPath_length radial).symm right
  have hgetInjective : Function.Injective ambient.edges.get :=
    List.nodup_iff_injective_get.mp
      (ambientRadialPath_isPath radial).isTrail.edges_nodup
  have hget :
      ambient.edges.get (Fin.cast ambient.length_edges.symm left') =
        ambient.edges.get (Fin.cast ambient.length_edges.symm right') := by
    rw [edges_get_cast_eq_s_getVert, edges_get_cast_eq_s_getVert]
    simpa [ambient, left', right', ambientRadialPathStepEdge] using
      congrArg Subtype.val hedge
  have hpositions : left' = right' :=
    Fin.cast_injective ambient.length_edges.symm (hgetInjective hget)
  exact Fin.cast_injective (ambientRadialPath_length radial).symm hpositions

/-- Actual L6 cuts whose radial-path edge meets the source's forbidden facial
zone. -/
def radialForbiddenCutPositions
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    Finset (Fin radial.path.length) :=
  Finset.univ.filter fun position =>
    ambientRadialPathStepEdge radial position.val position.isLt ∈
      radialForbiddenEdgeSupport embedded

@[simp] theorem mem_radialForbiddenCutPositions_iff
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : Fin radial.path.length) :
    position ∈ radialForbiddenCutPositions embedded radial ↔
      ambientRadialPathStepEdge radial position.val position.isLt ∈
        radialForbiddenEdgeSupport embedded := by
  simp [radialForbiddenCutPositions]

/-- Injecting each marked cut into its actual path edge bounds the number of
contaminated positions by the forbidden facial edge support. -/
theorem card_radialForbiddenCutPositions_le_edgeSupport
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    (radialForbiddenCutPositions embedded radial).card ≤
      (radialForbiddenEdgeSupport embedded).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun position : Fin radial.path.length =>
      ambientRadialPathStepEdge radial position.val position.isLt)
  · intro position hposition
    exact (mem_radialForbiddenCutPositions_iff embedded radial position).1
      hposition
  · exact (ambientRadialPathStepEdge_injective radial).injOn

/-- Source-facing cardinality bound for the actual contaminated radial cuts. -/
theorem card_radialForbiddenCutPositions_le
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    (radialForbiddenCutPositions embedded radial).card ≤
      radialForbiddenEdgeBudget embedded :=
  (card_radialForbiddenCutPositions_le_edgeSupport embedded radial).trans
    (card_radialForbiddenEdgeSupport_le embedded hdata geometry)

/-- **L6/L8 source assembly with constructed contamination.**  A sufficiently
long source instance now supplies its own two bad-position sets.  The size
premise is still expressed using the instance's weighted budget, so this is
not yet a uniform `V₀`; it is the exact source-derived length/depth entrance
that the high-curvature alternative must make uniform. -/
theorem Instance.exists_radialWitness_with_sourceLengthDepthOutcome
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (depthBound blockLength : Nat) (hblockLength : 0 < blockLength)
    (hlarge :
      2 * ((radialForbiddenEdgeBudget web.annular + 1) * blockLength + 1) <
        data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            ((radialForbiddenEdgeBudget web.annular + 1) * blockLength),
          RadialLengthDepthOutcome web.annular web.boundary_wellFormed
              witness.pair htriple
              (radialForbiddenCutPositions web.annular witness.pair.firstPath)
              (radialForbiddenEdgeBudget web.annular) depthBound blockLength ∨
            RadialLengthDepthOutcome web.annular web.boundary_wellFormed
              (swapRadialPathPair witness.pair) htriple
              (radialForbiddenCutPositions web.annular
                (swapRadialPathPair witness.pair).firstPath)
              (radialForbiddenEdgeBudget web.annular) depthBound blockLength := by
  let budget := radialForbiddenEdgeBudget web.annular
  let bound := (budget + 1) * blockLength
  have hbound : (budget + 1) * blockLength ≤ bound + 1 := by
    simp [bound]
  obtain ⟨majority, first, second, htriple, witness, houtcome⟩ :=
    exists_radialWitness_with_lengthDepthOutcome web
      bound budget depthBound blockLength hblockLength hbound (by
        simpa [bound, budget] using hlarge)
  have hbadFirst :
      (radialForbiddenCutPositions web.annular
        witness.pair.firstPath).card ≤ budget := by
    exact card_radialForbiddenCutPositions_le web.annular
      web.boundary_wellFormed web.geometry witness.pair.firstPath
  have hbadSecond :
      (radialForbiddenCutPositions web.annular
        (swapRadialPathPair witness.pair).firstPath).card ≤ budget := by
    exact card_radialForbiddenCutPositions_le web.annular
      web.boundary_wellFormed web.geometry
        (swapRadialPathPair witness.pair).firstPath
  refine ⟨majority, first, second, htriple, witness, ?_⟩
  simpa [bound, budget] using houtcome
    (radialForbiddenCutPositions web.annular witness.pair.firstPath)
    (radialForbiddenCutPositions web.annular
      (swapRadialPathPair witness.pair).firstPath)
    hbadFirst hbadSecond

end

end GoertzelV24ClosedWebRadialDefectPositions

end Mettapedia.GraphTheory.FourColor
