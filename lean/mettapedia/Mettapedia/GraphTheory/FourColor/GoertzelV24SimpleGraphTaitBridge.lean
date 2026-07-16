import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphTaitBridge

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FramedTrail
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For rotation data built from a finite simple graph, the faithful
rotation-system edge-adjacency graph is exactly the ordinary line graph. -/
theorem toRotationSystem_edgeAdjacencyGraph_eq_lineGraph
    (data : Data G) :
    data.toRotationSystem.edgeAdjacencyGraph = G.lineGraph := by
  ext first second
  rw [data.toRotationSystem.edgeAdjacencyGraph_adj_iff,
    SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, vertex, hfirst, hsecond⟩
    exact ⟨hne, vertex,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data first vertex).1 hfirst,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data second vertex).1 hsecond⟩
  · rintro ⟨hne, vertex, hfirst, hsecond⟩
    exact ⟨hne, vertex,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data first vertex).2 hfirst,
      (mem_simpleGraphRotationSystem_endpoints_iff
        data second vertex).2 hsecond⟩

/-- A graph-backed rotation system is Tait colorable exactly when its
underlying simple graph has an ordinary proper nonzero edge coloring. -/
theorem rotationSystemTaitColorable_iff_graphTaitColorable
    (data : Data G) :
    RotationSystemTaitColorable data.toRotationSystem ↔
      ∃ coloring : G.EdgeColoring Color,
        IsTaitEdgeColoring G coloring := by
  unfold RotationSystemTaitColorable
  change
    (∃ coloring : data.toRotationSystem.edgeAdjacencyGraph.Coloring Color,
      ∀ edge : G.edgeSet, coloring edge ≠ 0) ↔
    (∃ coloring : G.lineGraph.Coloring Color,
      ∀ edge : G.edgeSet, coloring edge ≠ 0)
  rw [toRotationSystem_edgeAdjacencyGraph_eq_lineGraph data]

/-- Rotation-system cubicity of graph-backed data is the exact local
three-incident-edge hypothesis used by the deleted-edge Trail bridge. -/
theorem incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic) :
    ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 := by
  intro vertex
  rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
  exact (data.toRotationSystem_isCubic_iff.mp hcubic) vertex

/-- The rotation-system noncolorability field of the current graph-backed
minimal-counterexample package is genuinely ordinary graph
noncolorability. -/
theorem graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    ¬ ∃ coloring : G.EdgeColoring Color,
        IsTaitEdgeColoring G coloring := by
  rw [← rotationSystemTaitColorable_iff_graphTaitColorable graphData]
  exact minimal.notColorable

/-- Any colored one-edge deletion of a graph-backed minimal counterexample
is an actual non-completable framed trail, even with every retained edge
movable. -/
theorem graphBackedVertexMinimalTaitCounterexample_deletedEdgeColoring_not_completable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {u v : V} (huv : G.Adj u v)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    ¬ FramedTangleCompletable (unrestrictedDeletedEdgeFrame G u v) C := by
  apply not_unrestrictedDeletedEdgeCompletable_of_not_taitColorable
    huv
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic)
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal)
    C hC

/-- Exact conditional contradiction at the current minimal-counterexample
interface. It isolates the two remaining Trail inputs without changing the
notion of graph colorability: a colorable edge deletion and completion of
its starting coloring. -/
theorem graphBackedVertexMinimalTaitCounterexample_false_of_deletedEdgeColorable_and_completable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {u v : V} (huv : G.Adj u v)
    (hdeletedColorable :
      ∃ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C)
    (hcompletable :
      ∀ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C →
          FramedTangleCompletable
            (unrestrictedDeletedEdgeFrame G u v) C) :
    False := by
  exact
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal)
      (exists_taitColoring_of_deletedEdgeColorable_and_completable
        huv
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic)
        hdeletedColorable hcompletable)

end

end GoertzelV24SimpleGraphTaitBridge

end Mettapedia.GraphTheory.FourColor
