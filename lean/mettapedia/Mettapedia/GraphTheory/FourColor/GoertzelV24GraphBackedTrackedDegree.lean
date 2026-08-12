import Mettapedia.GraphTheory.FourColor.GoertzelV24BetweenRegionDefectPaths
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge
import Mettapedia.GraphTheory.FourColor.RotationSystemTrackedEdgeGraph

/-!
# Ambient degree of graph-backed tracked strands

For a cubic graph-backed rotation system with a Tait coloring, every edge
carrying one of a valid pair of colors has exactly two neighbors in the
corresponding ambient tracked-edge graph.  This is the rotation-system form
of the ordinary bicolored-line-graph fact: one continuation leaves through
each endpoint of the selected edge.

The statement is deliberately ambient.  Restricting the graph to a corridor
prefix may make the degree odd; classifying the omitted neighbor as a named
source portal remains separate geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphTaitBridge

open GoertzelV24FramedTrail
open RotationSystem
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphBackedTrackedDegreeEdgeSetFintype :
    Fintype G.edgeSet :=
  G.fintypeEdgeSet

local instance graphBackedTrackedDegreeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

noncomputable local instance graphBackedTrackedDegreeNeighborFintype
    (data : Data G)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    Fintype
      ((data.toRotationSystem.trackedEdgeGraph coloring first second)
        |>.neighborSet edge) := by
  classical
  exact Subtype.fintype _

/-- A rotation-system coloring on graph-backed data, read as the identical
ordinary line-graph coloring. -/
noncomputable def graphEdgeColoringOfRotationColoring
    (data : Data G)
    (coloring : data.toRotationSystem.EdgeColoring Color) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk coloring.toFun <| by
    intro first second hadj
    apply coloring.valid
    rw [toRotationSystem_edgeAdjacencyGraph_eq_lineGraph data]
    exact hadj

@[simp]
theorem graphEdgeColoringOfRotationColoring_apply
    (data : Data G)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (edge : G.edgeSet) :
    graphEdgeColoringOfRotationColoring data coloring edge = coloring edge :=
  rfl

/-- The ambient tracked neighbor set of a selected graph-backed edge is
canonically equivalent to its neighbor set in the ordinary bicolored
line graph. -/
noncomputable def trackedNeighborEquivBicoloredNeighbor
    (data : Data G)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet)
    (hselected : IsTrackedColor first second (coloring edge)) :
    (data.toRotationSystem.trackedEdgeGraph coloring first second).neighborSet
        edge ≃
      ((graphEdgeColoringOfRotationColoring data coloring).bicoloredSubgraph
        first second).neighborSet ⟨edge, hselected⟩ := by
  let graphColoring := graphEdgeColoringOfRotationColoring data coloring
  let toBicolored :
      (data.toRotationSystem.trackedEdgeGraph coloring first second).neighborSet
          edge →
        (graphColoring.bicoloredSubgraph first second).neighborSet
          ⟨edge, hselected⟩ := fun neighbor => by
    have hadj := neighbor.2
    refine ⟨⟨neighbor.1, hadj.2.2⟩, ?_⟩
    change G.lineGraph.Adj edge neighbor.1
    rw [← toRotationSystem_edgeAdjacencyGraph_eq_lineGraph data]
    exact hadj.1
  let fromBicolored :
      (graphColoring.bicoloredSubgraph first second).neighborSet
          ⟨edge, hselected⟩ →
        (data.toRotationSystem.trackedEdgeGraph coloring first second).neighborSet
          edge := fun neighbor => by
    refine ⟨neighbor.1.1, ?_⟩
    have hadj : G.lineGraph.Adj edge neighbor.1.1 := neighbor.2
    refine ⟨?_, hselected, neighbor.1.2⟩
    rw [toRotationSystem_edgeAdjacencyGraph_eq_lineGraph data]
    exact hadj
  exact
    { toFun := toBicolored
      invFun := fromBicolored
      left_inv := by
        intro neighbor
        apply Subtype.ext
        rfl
      right_inv := by
        intro neighbor
        apply Subtype.ext
        apply Subtype.ext
        rfl }

/-- In a graph-backed cubic Tait coloring, every selected ambient tracked edge
has degree exactly two.  In particular its ambient degree is even. -/
theorem trackedEdgeGraph_degree_eq_two_of_cubic_tait
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    {first second : Color} (hpair : ValidColorPair first second)
    (edge : G.edgeSet)
    (hselected : IsTrackedColor first second (coloring edge)) :
    (data.toRotationSystem.trackedEdgeGraph coloring first second).degree edge =
      2 := by
  let graphColoring := graphEdgeColoringOfRotationColoring data coloring
  have hgraphTait : IsTaitEdgeColoring G graphColoring := by
    intro selected
    exact hcoloring selected
  have hgraphDegree :=
    bicoloredSubgraph_neighborSet_ncard_eq_two_of_endpoint_cubic
      graphColoring hgraphTait hpair edge hselected (by
        intro vertex _hvertex
        exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          data hcubic vertex)
  calc
    (data.toRotationSystem.trackedEdgeGraph coloring first second).degree edge =
        Fintype.card
          ((data.toRotationSystem.trackedEdgeGraph coloring first second)
            |>.neighborSet edge) :=
      ((data.toRotationSystem.trackedEdgeGraph coloring first second)
        |>.card_neighborSet_eq_degree edge).symm
    _ = ((data.toRotationSystem.trackedEdgeGraph coloring first second)
          |>.neighborSet edge).ncard :=
      Set.fintypeCard_eq_ncard _
    _ =
        (((graphColoring.bicoloredSubgraph first second).neighborSet
          ⟨edge, hselected⟩)).ncard :=
      Set.ncard_congr'
        (trackedNeighborEquivBicoloredNeighbor data coloring first second edge
          hselected)
    _ = 2 := hgraphDegree

theorem trackedEdgeGraph_degree_even_of_cubic_tait
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    {first second : Color} (hpair : ValidColorPair first second)
    (edge : G.edgeSet)
    (hselected : IsTrackedColor first second (coloring edge)) :
    Even
      ((data.toRotationSystem.trackedEdgeGraph coloring first second).degree
        edge) := by
  rw [trackedEdgeGraph_degree_eq_two_of_cubic_tait data hcubic coloring
    hcoloring hpair edge hselected]
  decide

end

end GoertzelV24SimpleGraphTaitBridge

end Mettapedia.GraphTheory.FourColor
