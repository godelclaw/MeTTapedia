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
open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
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
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

variable {data : AnnularBoundaryData G outerCount}

/-- Actual primal edges carried by all faces excluded from a source-clean
radial block. -/
def radialForbiddenEdgeSupport (embedded : ClosedWebAnnularEmbedding data) :
    Finset G.edgeSet := by
  classical
  exact embedded.corridorForbiddenFaces.biUnion fun face =>
    orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face.1

/-- A convenient explicit budget for the edge support of all forbidden
faces.  It retains the weighted-curvature dependence rather than replacing it
with the manuscript's invalid constant pentagon count. -/
def radialForbiddenEdgeBudget (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  embedded.boundaryCleanContaminationBudget *
    (interiorNegativeCurvatureWeight embedded + 6)

/-- The forbidden-face edge union is bounded by the already-computed number
of forbidden faces times the largest possible internal face boundary. -/
theorem card_radialForbiddenEdgeSupport_le
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    (radialForbiddenEdgeSupport embedded).card ≤
      radialForbiddenEdgeBudget embedded := by
  classical
  let weight := interiorNegativeCurvatureWeight embedded
  calc
    (radialForbiddenEdgeSupport embedded).card ≤
        ∑ face ∈ embedded.corridorForbiddenFaces,
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
            face.1).card := by
      unfold radialForbiddenEdgeSupport
      exact Finset.card_biUnion_le
    _ ≤ ∑ _face ∈ embedded.corridorForbiddenFaces, (weight + 6) := by
      apply Finset.sum_le_sum
      intro face hface
      exact internalFaceBoundary_card_le_weight_add_six embedded face.2
    _ = embedded.corridorForbiddenFaces.card * (weight + 6) := by
      simp
    _ ≤ embedded.boundaryCleanContaminationBudget * (weight + 6) :=
      Nat.mul_le_mul_right (weight + 6)
        (embedded.card_corridorForbiddenFaces_le_boundaryCleanContaminationBudget
          hdata geometry)
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
