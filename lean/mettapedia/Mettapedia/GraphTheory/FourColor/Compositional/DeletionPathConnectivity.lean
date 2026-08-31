import Mettapedia.GraphTheory.FiniteEdgePatchConnectivity
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathLocalization

/-!
# Finite component state along a coherent deletion path

The alternating graphs at two equal-absent-colour coordinates agree away
from the path footprint.  Rather than assuming that their distinguished
components are equal, this module records the exact finite state through
which those components can split or merge.

The nine-deletion footprint has at most forty-five edges and hence at most
ninety incident vertices.  After deleting those edges the endpoint
alternating graphs are literally equal.  Reachability between any two
footprint vertices factors through the common deleted graph and the
coordinate's exceptional-edge graph, so the component comparison is a
finite boundary relation.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivity

open AlternatingComponentLocalization
open AlternatingOverlapGeometry
open AlternatingSiteGeometry
open DeletionAtlasPath
open DeletionColorMatching
open DeletionSiteGeometry
open DeletionPathLocalization
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.Logic
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Value-level form of the union of the nine deletion footprints. -/
def pathFootprintValues
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    Finset (Sym2 V) :=
  (pathFootprint family).image Subtype.val

/-- Passing from ambient-edge subtypes to edge values does not enlarge the
path footprint. -/
theorem card_pathFootprintValues_le
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    (pathFootprintValues family).card ≤ 45 :=
  Finset.card_image_le.trans (card_pathFootprint_le family)

/-- Vertices incident with one of the path-footprint edges. -/
def pathBoundaryVertices
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) : Finset V :=
  SimpleGraph.edgeBoundaryVertices (pathFootprintValues family)

/-- The component interface of a nine-deletion path has at most ninety
vertices. -/
theorem card_pathBoundaryVertices_le
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    (pathBoundaryVertices family).card ≤ 90 := by
  calc
    (pathBoundaryVertices family).card ≤
        2 * (pathFootprintValues family).card :=
      SimpleGraph.card_edgeBoundaryVertices_le (pathFootprintValues family)
    _ ≤ 2 * 45 := Nat.mul_le_mul_left 2 (card_pathFootprintValues_le family)
    _ = 90 := by norm_num

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every selected deletion's restored central edge lies in the path
footprint. -/
theorem centralEdge_mem_pathFootprint
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 9) :
    centralEdge (family.data index) ∈ pathFootprint family := by
  apply Finset.mem_biUnion.2
  exact ⟨index, Finset.mem_univ _, by simp [deletionFootprint]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Value-level form of `centralEdge_mem_pathFootprint`. -/
theorem centralEdgeValue_mem_pathFootprintValues
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 9) :
    centralEdgeValue (family.data index) ∈ pathFootprintValues family := by
  exact Finset.mem_image.2
    ⟨centralEdge (family.data index),
      centralEdge_mem_pathFootprint family index, rfl⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The first endpoint of every selected central edge is a boundary vertex
of the finite component interface. -/
theorem firstVertex_mem_pathBoundaryVertices
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 9) :
    (family.data index).firstVertex ∈ pathBoundaryVertices family := by
  apply (SimpleGraph.mem_edgeBoundaryVertices _ _).2
  exact ⟨centralEdgeValue (family.data index),
    centralEdgeValue_mem_pathFootprintValues family index,
    by simp [centralEdgeValue]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The second endpoint of every selected central edge is also a boundary
vertex of the finite component interface. -/
theorem secondVertex_mem_pathBoundaryVertices
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 9) :
    (family.data index).secondVertex ∈ pathBoundaryVertices family := by
  apply (SimpleGraph.mem_edgeBoundaryVertices _ _).2
  exact ⟨centralEdgeValue (family.data index),
    centralEdgeValue_mem_pathFootprintValues family index,
    by simp [centralEdgeValue]⟩

/-- The alternating graph at one coordinate of a coherent deletion path. -/
def pathAlternatingGraph
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G) (index : Fin 9) :
    SimpleGraph V :=
  alternatingGraph minimizer.pairing
    ((matchingState rotation minimal family pathSection index).pairing
      (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
        rotation minimal))

/-- Every path alternating graph is an ambient subgraph. -/
theorem pathAlternatingGraph_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G) (index : Fin 9) :
    pathAlternatingGraph rotation minimal family pathSection minimizer index ≤ G := by
  apply alternatingGraph_le
  · exact minimizer.supported
  · exact (matchingState rotation minimal family pathSection index).pairing_supported
      (ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal)

/-- Equal-absent-colour endpoint alternating graphs become literally equal
after deleting the path footprint. -/
theorem pathAlternatingGraphs_deleteFootprint_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (first second : Fin 9)
    (habsent :
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor) :
    (pathAlternatingGraph rotation minimal family pathSection minimizer first).deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) =
      (pathAlternatingGraph rotation minimal family pathSection minimizer second).deleteEdges
        (pathFootprintValues family : Set (Sym2 V)) := by
  let sourceGraph :=
    pathAlternatingGraph rotation minimal family pathSection minimizer first
  let targetGraph :=
    pathAlternatingGraph rotation minimal family pathSection minimizer second
  have hsourceLe : sourceGraph ≤ G :=
    pathAlternatingGraph_le rotation minimal family pathSection minimizer first
  have htargetLe : targetGraph ≤ G :=
    pathAlternatingGraph_le rotation minimal family pathSection minimizer second
  ext left right
  simp only [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hsource, houtside⟩
    let edge : G.edgeSet :=
      ⟨s(left, right), G.mem_edgeSet.mpr (hsourceLe hsource)⟩
    have houtside' : edge ∉ pathFootprint family := by
      intro hmem
      exact houtside (Finset.mem_image.2 ⟨edge, hmem, rfl⟩)
    have hagrees := alternatingGraphs_agree_outside_pathFootprint
      rotation minimal family pathSection minimizer.pairing first second
        habsent edge houtside'
    exact ⟨targetGraph.mem_edgeSet.mp
      (hagrees.mp (sourceGraph.mem_edgeSet.mpr hsource)), houtside⟩
  · rintro ⟨htarget, houtside⟩
    let edge : G.edgeSet :=
      ⟨s(left, right), G.mem_edgeSet.mpr (htargetLe htarget)⟩
    have houtside' : edge ∉ pathFootprint family := by
      intro hmem
      exact houtside (Finset.mem_image.2 ⟨edge, hmem, rfl⟩)
    have hagrees := alternatingGraphs_agree_outside_pathFootprint
      rotation minimal family pathSection minimizer.pairing first second
        habsent edge houtside'
    exact ⟨sourceGraph.mem_edgeSet.mp
      (hagrees.mpr (targetGraph.mem_edgeSet.mpr htarget)), houtside⟩

/-- The finite carrier on which component changes along the deletion path are
visible. -/
abbrev PathBoundary
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :=
  SimpleGraph.EdgeBoundary (pathFootprintValues family)

/-- One step of the exact component state: travel either through the common
deleted graph or through the coordinate-specific exceptional patch. -/
abbrev pathBoundaryStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G) (index : Fin 9)
    (left right : PathBoundary family) : Prop :=
  ((pathAlternatingGraph rotation minimal family pathSection minimizer index).deleteEdges
      (pathFootprintValues family : Set (Sym2 V))).Reachable left right ∨
    (SimpleGraph.exceptionalEdgeGraph
      (pathAlternatingGraph rotation minimal family pathSection minimizer index)
      (pathFootprintValues family)).Reachable left right

set_option maxHeartbeats 800000 in
/-- Complete finite-state factorization of component membership at any one
coordinate. -/
theorem pathAlternatingGraph_reachable_iff_boundaryClosure
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G) (index : Fin 9)
    {left right : V}
    (hleft : left ∈ pathBoundaryVertices family)
    (hright : right ∈ pathBoundaryVertices family) :
    (pathAlternatingGraph rotation minimal family pathSection minimizer index).Reachable
        left right ↔
      Relation.ReflTransGen
        (pathBoundaryStep rotation minimal family pathSection minimizer index)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  exact SimpleGraph.reachable_iff_edgeBoundaryClosure
    (pathAlternatingGraph rotation minimal family pathSection minimizer index)
    (pathFootprintValues family) hleft hright

set_option maxHeartbeats 800000 in
/-- Component equality between any two selected central roots is read
exactly from the at-most-ninety-vertex boundary closure. -/
theorem selectedFirstVertices_component_eq_iff_boundaryClosure
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (coordinate first second : Fin 9) :
    let graph := pathAlternatingGraph
      rotation minimal family pathSection minimizer coordinate
    graph.connectedComponentMk (family.data first).firstVertex =
        graph.connectedComponentMk (family.data second).firstVertex ↔
      Relation.ReflTransGen
        (pathBoundaryStep rotation minimal family pathSection minimizer coordinate)
        ⟨(family.data first).firstVertex,
          firstVertex_mem_pathBoundaryVertices family first⟩
        ⟨(family.data second).firstVertex,
          firstVertex_mem_pathBoundaryVertices family second⟩ := by
  dsimp only
  rw [SimpleGraph.ConnectedComponent.eq]
  exact pathAlternatingGraph_reachable_iff_boundaryClosure
    rotation minimal family pathSection minimizer coordinate
      (firstVertex_mem_pathBoundaryVertices family first)
      (firstVertex_mem_pathBoundaryVertices family second)

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivity
