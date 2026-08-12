import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoDefectParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphTaitBridge

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FramedTrail
open GoertzelV24TwoDefectParity
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

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

/-- A graph-backed vertex-minimal Tait counterexample has no Tait-colorable
one-edge deletion. Indeed, two-defect parity would extend any such coloring
back across the deleted edge. -/
theorem graphBackedVertexMinimalTaitCounterexample_deletedEdge_not_taitColorable
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {u v : V} (huv : G.Adj u v) :
    ¬ ∃ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C := by
  exact deletedEdge_not_taitColorable_of_not_taitColorable
    huv
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic)
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal)

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

/-! The final Trail-Completability input is uniform in the chosen deleted
edge. Naming that input here makes the endgame contract explicit: the
geometric/combinatorial work must prove this predicate, while the graph-side
minimal-counterexample contradiction is already closed. In particular, this
is not a new existence claim and it does not choose a classical finite
catalogue. -/

def UniformDeletedEdgeTrailCompletability
    : Prop :=
  ∀ {u v : V}, G.Adj u v →
    ∀ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
      IsTaitEdgeColoring (DeletedEdgeGraph G u v) C →
        FramedTangleCompletable
          (unrestrictedDeletedEdgeFrame G u v) C

theorem graphBackedVertexMinimalTaitCounterexample_false_of_uniformDeletedEdgeTrailCompletability
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcompletion : UniformDeletedEdgeTrailCompletability (G := G))
    {u v : V} (huv : G.Adj u v)
    (hdeletedColorable :
      ∃ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    False := by
  exact graphBackedVertexMinimalTaitCounterexample_false_of_deletedEdgeColorable_and_completable
    graphData minimal huv hdeletedColorable (fun C hC => hcompletion huv C hC)

end

end GoertzelV24SimpleGraphTaitBridge

end Mettapedia.GraphTheory.FourColor
